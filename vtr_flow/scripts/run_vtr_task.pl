#!/usr/bin/perl
###################################################################################
# This script executes one or more VTR tasks
#
# Usage:
#	run_vtr_task.pl <task_name1> <task_name2> ... [OPTIONS]
#
# Options:
#   -s <script_params>:  Treat the remaining command line options as parameters
#               to forward to the VPR calling script (e.g. run_vtr_flow.pl).
# 	-p <N>:  Perform parallel execution using N threads. Note: Large benchmarks
#				will use very large amounts of memory (several gigabytes). Because
#				of this, parallel execution often saturates the physical memory,
#				requiring the use of swap memory, which will cause slower
#				execution. Be sure you have allocated a sufficiently large swap
#				memory or errors may result.
#   -j <N>: Same as -p <N>
#	-l <task_list_file>:  A file containing a list of tasks to execute. Each task
#							name should be on a separate line.
#
#	-hide_runtime: Do not show runtime estimates
#
# Note: At least one task must be specified, either directly as a parameter or
#		through the -l option.
#
# Authors: Jason Luu and Jeff Goeders
#
###################################################################################

use strict;

# This loads the thread libraries, but within an eval so that if they are not available
# the script will not fail.  If successful, $threaded = 1
my $threaded = eval 'use threads; use Thread::Queue; 1';

use Cwd;
use File::Spec;
use File::Basename;
use File::Path qw(make_path);
use List::MoreUtils qw(uniq);
use POSIX qw(strftime);

# Function Prototypes
sub trim;
sub run_single_task;
sub do_work;
sub get_result_file_metrics;
sub ret_expected_runtime;
sub ret_expected_min_W;
sub ret_expected_vpr_status;

# Get Absolute Path of 'vtr_flow
Cwd::abs_path($0) =~ m/(.*vtr_flow)/;
my $vtr_flow_path = $1;

my @tasks;
my @task_files;
my $token;
my $processors             = 1;
my $run_prefix             = "run";
my $show_runtime_estimates = 1;
my $system_type            = "local";
my $shared_script_params   = "";
my $verbosity              = 0;

# Parse Input Arguments
while ( $token = shift(@ARGV) ) {

	# Check for -pN
	if ( $token =~ /^-p(\d+)$/ ) {
		$processors = int($1);
	}

	# Check for -jN
	if ( $token =~ /^-j(\d+)$/ ) {
		$processors = int($1);
	}

	# Check for -p N or -j N
	elsif ( $token eq "-p" or $token eq "-j" ) {
		$processors = int( shift(@ARGV) );
	}

	elsif ( $token eq "-verbosity") {
		$verbosity = int( shift(@ARGV) );
	}

    # Treat the remainder of the command line options as script parameters shared by all tasks
    elsif ( $token eq "-s" ) {
        $shared_script_params = join(' ', @ARGV);
        while ($token = shift(@ARGV)) {
            print "adding to shared script params: $token\n"
        }
        print "shared script params: $shared_script_params\n"
    }

	elsif ( $token eq "-system" ) {
		$system_type = shift(@ARGV);
	}

	# Check for a task list file
	elsif ( $token =~ /^-l(.+)$/ ) {
		push( @task_files, expand_user_path($1) );
	}
	elsif ( $token eq "-l" ) {
		push( @task_files, expand_user_path( shift(@ARGV) ) );
	}

	elsif ( $token eq "-hide_runtime" ) {
		$show_runtime_estimates = 0;
	}

	elsif ( $token =~ /^-/ ) {
		die "Invalid option: $token\n";
	}

	# must be a task name
	else {
		if ( $token =~ /(.*)\/$/ ) {
			$token = $1;
		}
		push( @tasks, $token );
	}
}

# Check threaded
if ( $processors > 1 and not $threaded ) {
	print
	  "Multithreaded option specified, but is not supported by this version of perl.  Execution will be single threaded.\n";
	$processors = 1;
}

# Read Task Files
foreach (@task_files) {
	open( FH, $_ ) or die "$! ($_)\n";
	while (<FH>) {
		push( @tasks, $_ );
	}
	close(FH);
}

# Remove duplicate tasks, use uniq() to preserve ordering
@tasks = uniq(@tasks);

#print "Processors: $processors\n";
#print "Tasks: @tasks\n";

if ( $#tasks == -1 ) {
	die "\n"
	  . "Incorrect usage.  You must specify at least one task to execute\n"
	  . "\n"
	  . "USAGE:\n"
	  . "run_vtr_task.pl <TASK1> <TASK2> ... \n" . "\n"
	  . "OPTIONS:\n"
	  . "-l <path_to_task_list.txt> - Provides a text file with a list of tasks\n"
	  . "-p <N> - Execution is performed in parallel using N threads (Default: 1)\n";
}

##############################################################
# Run tasks
##############################################################

#Collect the actions for all tasks
my @all_task_actions;
foreach my $task (@tasks) {
	chomp($task);
	my $task_actions = generate_single_task_actions($task);
    push(@all_task_actions, @$task_actions);
}

#Run all the actions (potentially in parallel)
my $num_total_failures = run_actions(\@all_task_actions);

exit $num_total_failures;

##############################################################
# Subroutines
##############################################################

sub generate_single_task_actions {
	my $circuits_dir;
	my $archs_dir;
	my $sdc_dir        = "sdc";
	my $script_default = "run_vtr_flow.pl";
	my $script         = $script_default;
	my $script_path;
	my $script_params_common = $shared_script_params;  # start with the shared ones then build unique ones
	my @circuits_list;
	my @archs_list;
	my @script_params_list;
	my $cmos_tech_path = "";

	my $task     = shift(@_);
	(my $task_dir = "$vtr_flow_path/tasks/$task") =~ s/\s+$//; # trim right white spaces for chdir to work on Windows
	chdir($task_dir) or die "Task directory does not exist ($task_dir): $!\n";

	# Get Task Config Info

	my $task_config_file_path = "config/config.txt";
	open( CONFIG_FH, $task_config_file_path )
	  or die
	  "Cannot find task configuration file ($task_dir/$task_config_file_path)";
	while (<CONFIG_FH>) {
		my $line = $_;
		chomp($line);

        #Skip comment-only or blank lines
		if ( $line =~ /^\s*#.*$/ or $line =~ /^\s*$/ ) { next; }

        #Trim off a line-ending comment
        $line =~ s/#.*$//;

		my @data  = split( /=/, $line );
		my $key   = trim( $data[0] );
		my $value = trim( $data[1] );
		if ( $key eq "circuits_dir" ) {
			$circuits_dir = $value;
		} elsif ( $key eq "archs_dir" ) {
			$archs_dir = $value;
		} elsif ( $key eq "sdc_dir" ) {
			$sdc_dir = $value;
		} elsif ( $key eq "circuit_list_add" ) {
			push( @circuits_list, $value );
		} elsif ( $key eq "arch_list_add" ) {
			push( @archs_list, $value );
		} elsif ( $key eq "script_params_list_add" ) {
			push( @script_params_list, $value );
		} elsif ( $key eq "script_path" ) {
			$script = $value;
		} elsif ( $key eq "script_params" || $key eq "script_params_common") {
			$script_params_common .= ' ' . $value;
		} elsif ( $key eq "cmos_tech_behavior" ) {
			$cmos_tech_path = $value;
		} elsif ($key eq "parse_file"
			or $key eq "qor_parse_file"
			or $key eq "pass_requirements_file" )
		{

			#Used by parser
		}
		else {
			die "Invalid option (" . $key . ") in configuration file.";
		}
	}

	# Using default script
	if ( $script eq $script_default ) {

		# This is hack to automatically add the option '-temp_dir .' if using the run_vtr_flow.pl script
		# This ensures that a 'temp' folder is not created in each circuit directory
		if ( !( $script_params_common =~ /-temp_dir/ ) ) {
            #-temp_dir must come before the script_params, so that it gets picked up by run_vtr_flow
            # and not passed on as an argument to a tool (e.g. VPR)
 			$script_params_common = " -temp_dir . " . $script_params_common;
		}
	}
	else {
		$show_runtime_estimates = 0;
	}

	$circuits_dir = expand_user_path($circuits_dir);
	$archs_dir    = expand_user_path($archs_dir);
	$sdc_dir      = expand_user_path($sdc_dir);

	if ( -d "$vtr_flow_path/$circuits_dir" ) {
		$circuits_dir = "$vtr_flow_path/$circuits_dir";
	}
	elsif ( -d $circuits_dir ) {
	}
	else {
		die "Circuits directory not found ($circuits_dir)";
	}

	if ( -d "$vtr_flow_path/$archs_dir" ) {
		$archs_dir = "$vtr_flow_path/$archs_dir";
	}
	elsif ( -d $archs_dir ) {
	}
	else {
		die "Archs directory not found ($archs_dir)";
	}

	if ( -d "$vtr_flow_path/$sdc_dir" ) {
		$sdc_dir = "$vtr_flow_path/$sdc_dir";
	}
	elsif ( -d $sdc_dir ) {
	}
	else {
		$sdc_dir = "$vtr_flow_path/sdc";
	}

	(@circuits_list) or die "No circuits specified for task $task";
	(@archs_list)    or die "No architectures specified for task $task";

    if (!@script_params_list) {
        #Add a default empty param if none otherwise specified
        #(i.e. only base params)
        push(@script_params_list, "");
    }

	# Check script
	$script = expand_user_path($script);
	if ( -e "$task_dir/config/$script" ) {
		$script_path = "$task_dir/config/$script";
	}
	elsif ( -e "$vtr_flow_path/scripts/$script" ) {
		$script_path = "$vtr_flow_path/scripts/$script";
	}
	elsif ( -e $script ) {
	}
	else {
		die
		  "Cannot find script for task $task ($script).  Looked for $task_dir/config/$script or $vtr_flow_path/scripts/$script";
	}

    # Check architectures
    foreach my $arch (@archs_list) {
        (-f "$archs_dir/$arch") or die "Architecture file not found ($archs_dir/$arch)";
    }

    # Check circuits
    foreach my $circuit (@circuits_list) {
        (-f "$circuits_dir/$circuit") or die "Circuit file not found ($circuits_dir/$circuit)";
    }

	# Check CMOS tech behavior
	if ( $cmos_tech_path ne "" ) {
		$cmos_tech_path = expand_user_path($cmos_tech_path);
		if ( -e "$task_dir/config/$cmos_tech_path" ) {
			$cmos_tech_path = "$task_dir/config/$cmos_tech_path";
		}
		elsif ( -e "$vtr_flow_path/tech/$cmos_tech_path" ) {
			$cmos_tech_path = "$vtr_flow_path/tech/$cmos_tech_path";
		}
		elsif ( -e $cmos_tech_path ) {
		}
		else {
			die
			  "Cannot find CMOS technology behavior file for $task ($script). Looked for $task_dir/config/$cmos_tech_path or $vtr_flow_path/tech/$cmos_tech_path";
		}
		$script_params_common .= " -cmos_tech $cmos_tech_path";
	}

	# Check if golden file exists
	my $golden_results_file = "$task_dir/config/golden_results.txt";

	##############################################################
	# Create a new experiment directory to run experiment in
	# Counts up until directory number doesn't exist
	##############################################################
	my $experiment_number = 0;

    my $run_dir = "";
    my $run_dir_no_prefix = "";
    do {
        $experiment_number += 1;
        $run_dir = sprintf("run%03d", $experiment_number);
        $run_dir_no_prefix = sprintf("run%d", $experiment_number);
    } while (-e $run_dir or -e $run_dir_no_prefix);

	mkdir( $run_dir, 0775 ) or die "Failed to make directory ($run_dir): $!";
	chmod( 0775, $run_dir );
	chdir($run_dir) or die "Failed to change to directory ($run_dir): $!";

	##############################################################
    # Build up the list of commands to run
	##############################################################
    my @actions;
    foreach my $circuit (@circuits_list) {
        foreach my $arch (@archs_list) {
            foreach my $params (@script_params_list) {

                my $full_params = $script_params_common;
                my $full_params_dirname = "common";
                if ($params ne "") {
                    $full_params .= " " . $params;
                    $full_params_dirname .= "_" . $params;
                    $full_params_dirname =~ s/ /_/g; #Convert spaces to underscores for directory name
                }

                #Determine the directory where to run
                my $dir = "$task_dir/$run_dir/${arch}/${circuit}/${full_params_dirname}";

                my $name = "'${task}: ${arch}/${circuit}/${full_params_dirname}'";

                #Do we expect a specific status?
                my $expect_fail = "";
                my $expected_vpr_status = ret_expected_vpr_status($circuit, $arch, $full_params_dirname, $golden_results_file);
                if ($expected_vpr_status ne "success" and $expected_vpr_status ne "Unkown") {
                    $expect_fail = "-expect_fail";
                }

                #Build the command to run
                my $command = "$script_path $circuits_dir/$circuit $archs_dir/$arch $expect_fail -name $name $full_params";

                #Determine the SDC file name
                my $sdc_name = fileparse( $circuit, '\.[^.]+$' ) . ".sdc";
                my $sdc = "$sdc_dir/$sdc_name";
                if( -r $sdc) {
                    $command .= " --sdc_file $sdc";
                }

                #Add a hint about the minimum channel width (potentially saves run-time)
                my $expected_min_W = ret_expected_min_W($circuit, $arch, $full_params_dirname, $golden_results_file);
                if($expected_min_W > 0) {
                    $command .= " --min_route_chan_width_hint $expected_min_W";
                }

                #Estimate runtime
                my $runtime_estimate = ret_expected_runtime($circuit, $arch, $full_params_dirname, $golden_results_file);

                my @action = [$dir, $command, $runtime_estimate];
                push(@actions, @action);
            }
        }
    }

	##############################################################
	# Run experiment
	##############################################################
    my $num_failures = 0;


    return \@actions;
}

sub run_actions {
    my ($actions) = @_;

    my $num_failures = 0;

	if ( $system_type eq "local" ) {
        my $thread_work   = Thread::Queue->new();
        my $thread_result = Thread::Queue->new();
        my $thread_return_code = Thread::Queue->new();
        my $threads       = $processors;

        foreach my $action (@$actions) {
            my ($run_dir, $command, $runtime_estimate) = @$action;

            if ($verbosity > 0) {
                print "$command\n";
            }
            $thread_work->enqueue("$run_dir||||$command");

        }

        my @pool = map { threads->create( \&do_work, $thread_work, $thread_result, $thread_return_code ) } 1 .. $threads;

        for ( 1 .. $threads ) {
            while ( my $result = $thread_result->dequeue ) {
                chomp($result);
                print $result . "\n";
            }
            while (my $return_code = $thread_return_code->dequeue) {
                if($return_code != 0) {
                    $num_failures += 1;
                }
            }
        }

        $_->join for @pool;
	} else {
        die("Unrecognized job system '$system_type'");
    }

    return $num_failures;
}

sub do_work {
	my ( $work_queue, $return_queue, $return_code_queue ) = @_;
	my $tid = threads->tid;

	while (1) {
		my $work    = $work_queue->dequeue_nb();
		my @work    = split( /\|\|\|\|/, $work );
		my $dir     = @work[0];
		my $command = @work[1];

		if ( !$dir ) {
			last;
		}

		make_path( "$dir", { mode => 0775 } ) or die "Failed to create directory ($dir): $!";
		my $return_status = system "cd $dir; $command > vtr_flow.out";
        my $exit_code = $return_status >> 8; #Shift to get real exit code

		open( OUT_FILE, "$dir/vtr_flow.out" ) or die "Cannot open $dir/vtr_flow.out: $!";
		my $sys_output = do { local $/; <OUT_FILE> };

		#$sys_output =~ s/\n//g;
		$return_queue->enqueue($sys_output);

        $return_code_queue->enqueue($exit_code);
	}
    #Need to put undef in queues to indicate end and prevent blocking forever
	$return_queue->enqueue(undef);
    $return_code_queue->enqueue(undef);

	#print "$tid exited loop\n"
}

# trim whitespace
sub trim($) {
	my $string = shift;
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	return $string;
}

sub expand_user_path {
	my $str = shift;
	$str =~ s/^~\//$ENV{"HOME"}\//;
	return $str;
}

#Returns a hash mapping the name to column index in the results file
sub get_result_file_keys {
    my ($results_file_path) = @_;

    my %index;

    if ( -r $results_file_path) {

        #Load the results file
        open( RESULTS, $results_file_path );
        my @lines = <RESULTS>;
        close(RESULTS);

        my $header_line = shift(@lines);
        my @headers     = map(trim($_), split( /\t/, $header_line ));

        #Build hash look-up from name to index
        @index{@headers} = ( 0 .. $#headers );
    }

    return %index;
}

#Returns a hash corresponding to the first row from a parse_results.txt/golden_results.txt file
#which matches the given set of keys.
#
#If none is found, returns an empty hash
sub get_result_file_metrics {
    my ($results_file_path, $keys_ref) = @_;
    my %keys = %{$keys_ref};

    my %metrics;

    if ( -r $results_file_path) {

        my %index = get_result_file_keys($results_file_path);

        #Skip checking for script_params if not included in the results file
        #
        #Note that this is a temporary work-around since not all golden results have been
        #updated to record the script params
        #
        #TODO: Once all golden results updated, remove this check to unconditionally
        #check for script params
        if (not exists $index{'script_params'}) {
            delete $keys{'script_params'};
        }

        #Check that the required keys exist
        my $missing_keys = 0;
        foreach my $key (keys %keys) {

            if (not exists $index{$key}) {
                $missing_keys++;
            }
        }

        if ($missing_keys == 0) {

            #Load the results file
            open( RESULTS, $results_file_path );
            my @lines = <RESULTS>;
            close(RESULTS);

            #Find the entry which matches the key values
            my @line_array;
            foreach my $line (@lines) {
                @line_array = map(trim($_), split( /\t/, $line ));

                #Check all key values match
                my $found = 1;
                foreach my $key (keys %keys) {
                    my $value = @line_array[$index{$key}];

                    if ($value ne $keys{$key}) {
                        $found = 0;
                        last;
                    }
                }

                if ($found) {
                    #Matching row, build hash of entry row
                    for my $metric_name (keys %index) {
                        $metrics{$metric_name} = @line_array[$index{$metric_name}];
                    }
                    last;
                }
            }
        }
    }

    return %metrics;
}

sub ret_expected_runtime {
	my $circuit_name             = shift;
	my $arch_name                = shift;
    my $script_params            = shift;
	my $golden_results_file_path = shift;
	my $seconds                  = 0;

    my %keys = (
        "arch" => $arch_name,
        "circuit" => $circuit_name,
        "script_params" => $script_params,
    );

    my %metrics = get_result_file_metrics($golden_results_file_path, \%keys);

    if (not exists $metrics{'vtr_flow_elapsed_time'}) {
        return "Unkown";
    }

    $seconds = $metrics{'vtr_flow_elapsed_time'};
    if ( $seconds < 60 ) {
        my $str = sprintf( "%.0f seconds", $seconds );
        return $str;
    } elsif ( $seconds < 3600 ) {
        my $min = $seconds / 60;
        my $str = sprintf( "%.0f minutes", $min );
        return $str;
    } else {
        my $hour = $seconds / 60 / 60;
        my $str = sprintf( "%.0f hours", $hour );
        return $str;
    }
}

sub ret_expected_min_W {
	my $circuit_name             = shift;
	my $arch_name                = shift;
    my $script_params            = shift;
	my $golden_results_file_path = shift;

    my %keys = (
        "arch" => $arch_name,
        "circuit" => $circuit_name,
        "script_params" => $script_params,
    );

    my %metrics = get_result_file_metrics($golden_results_file_path, \%keys);

    if (not exists $metrics{'min_chan_width'}) {
        return -1;
    }

    return $metrics{'min_chan_width'};
}

sub ret_expected_vpr_status {
	my $circuit_name             = shift;
	my $arch_name                = shift;
    my $script_params            = shift;
	my $golden_results_file_path = shift;

    my %keys = (
        "arch" => $arch_name,
        "circuit" => $circuit_name,
        "script_params" => $script_params,
    );

    my %metrics = get_result_file_metrics($golden_results_file_path, \%keys);

    if (not exists $metrics{'vpr_status'}) {
        return "Unkown";
    }

    return $metrics{'vpr_status'};
}


/*This function loads in a routing resource graph written in xml format
 * into vpr when the option --read_rr_graph <file name> is specified.
 * When it is not specified the build_rr_graph function is then called.
 * This is done using the libpugixml library. This is useful
 * when specific routing resources should remain constant or when
 * some information left out in the architecture can be specified
 * in the routing resource graph. The routing resource graph file is
 * contained in a <rr_graph> tag. Its subtags describe the rr graph's
 * various features such as nodes, edges, and segments. Information such
 * as blocks, grids, and segments are verified with the architecture
 * to ensure it matches. An error will through if any feature does not match.
 * Other elements such as edges, nodes, and switches
 * are overwritten by the rr graph file if one is specified. If an optional
 * identifier such as capacitance is not specified, it is set to 0*/

#include <string.h>
#include <algorithm>
#include <ctime>
#include <fstream>
#include <sstream>
#include <iostream>
#include <utility>

#include "vtr_version.h"
#include "vtr_assert.h"
#include "vtr_util.h"
#include "vtr_memory.h"
#include "vtr_math.h"
#include "vtr_log.h"
#include "vtr_time.h"

#include "pugixml.hpp"
#include "pugixml_util.hpp"
#include "read_xml_arch_file.h"
#include "read_xml_util.h"
#include "globals.h"
#include "rr_graph.h"
#include "rr_graph2.h"
#include "rr_metadata.h"
#include "rr_graph_indexed_data.h"
#include "rr_graph_writer.h"
#include "check_rr_graph.h"
#include "echo_files.h"

#include "vpr_types.h"
#include "vpr_utils.h"
#include "vpr_error.h"

#include "rr_graph_reader.h"

#include "rr_graph_uxsdcxx.h"
#include "serdes_utils.h"
#include "mmap_file.h"
#include "capnp/message.h"
#include "capnp/serialize.h"
#include "rr_graph_uxsdcxx.capnp.h"

/*********************** Subroutines local to this module *******************/
void load_rr_file_xml(const t_graph_type graph_type,
                      const DeviceGrid& grid,
                      const std::vector<t_segment_inf>& segment_inf,
                      const enum e_base_cost_type base_cost_type,
                      int* wire_to_rr_ipin_switch,
                      const char* read_rr_graph_name);
void load_rr_file_capnp(const t_graph_type graph_type,
                        const DeviceGrid& grid,
                        const std::vector<t_segment_inf>& segment_inf,
                        const enum e_base_cost_type base_cost_type,
                        int* wire_to_rr_ipin_switch,
                        const char* read_rr_graph_name);
void process_nodes_xml(uxsd::rr_graph& rr_graph);
void process_edges_xml(uxsd::rr_graph& rr_graph, int* wire_to_rr_ipin_switch);
void process_seg_id_xml(uxsd::rr_graph& rr_graph);
void set_cost_indices_xml(uxsd::rr_graph& rr_graph, const bool is_global_graph, const int num_seg_types);
void process_nodes_capnp(ucap::RrGraph::Reader& rr_graph);
void process_edges_capnp(ucap::RrGraph::Reader& rr_graph, int* wire_to_rr_ipin_switch);
void process_seg_id_capnp(ucap::RrGraph::Reader& rr_graph);
void set_cost_indices_capnp(ucap::RrGraph::Reader& rr_graph, const bool is_global_graph, const int num_seg_types);
void process_rr_node_indices(const DeviceGrid& grid);

/************************ Subroutine definitions ****************************/

static int pin_index_by_num(const t_class& class_inf, int num) {
    for (int index = 0; index < class_inf.num_pins; ++index) {
        if (num == class_inf.pinlist[index]) {
            return index;
        }
    }
    return -1;
}

/**
 * Loads the given RR_graph file into the appropriate data structures
 * as specified by read_rr_graph_name. Sets up correct routing data
 * structures as well.
 *
 * If the given file_name has an .xml extension, it attempts to read it
 * using uxsdcxx's XML schema generated code.
 * If it has a .rr_graph extension, it attempts to read a Cap'n Proto
 * message, the schema for which is generated from the XML schema.
 * Otherwise, it prints a warning and tries to read as an XML file.
 */
void load_rr_file(const t_graph_type graph_type,
                  const DeviceGrid& grid,
                  const std::vector<t_segment_inf>& segment_inf,
                  const enum e_base_cost_type base_cost_type,
                  int* wire_to_rr_ipin_switch,
                  const char* read_rr_graph_name) {
    if (vtr::check_file_name_extension(read_rr_graph_name, ".xml")) {
        load_rr_file_xml(graph_type, grid, segment_inf, base_cost_type,
                                      wire_to_rr_ipin_switch, read_rr_graph_name);
    } else if (vtr::check_file_name_extension(read_rr_graph_name, ".rr_graph")) {
        load_rr_file_capnp(graph_type, grid, segment_inf, base_cost_type,
                                          wire_to_rr_ipin_switch, read_rr_graph_name);
    } else {
        VTR_LOG_WARN(
            "RR graph file '%s' may be in incorrect format. "
            "Expecting .xml or .rr_graph extensions.\n",
            read_rr_graph_name);
        load_rr_file_xml(graph_type, grid, segment_inf, base_cost_type,
                                      wire_to_rr_ipin_switch, read_rr_graph_name);
    }
}

/**
 * Load a XML rr_graph.
 */
void load_rr_file_xml(const t_graph_type graph_type,
                      const DeviceGrid& grid,
                      const std::vector<t_segment_inf>& segment_inf,
                      const enum e_base_cost_type base_cost_type,
                      int* wire_to_rr_ipin_switch,
                      const char* read_rr_graph_name) {
    auto& device_ctx = g_vpr_ctx.mutable_device();

    if (vtr::check_file_name_extension(read_rr_graph_name, ".xml") == false) {
        VTR_LOG_WARN(
            "RR graph file '%s' may be in incorrect format. "
            "Expecting .xml format\n",
            read_rr_graph_name);
    }

    /* zero-initialize the thing */
    uxsd::rr_graph rr_graph = uxsd::rr_graph();
    std::ifstream is;
    is.open(read_rr_graph_name);

    vtr::ScopedStartFinishTimer timer("Loading routing resource graph");
    pugi::xml_parse_result result = rr_graph.load(is);
    if (!result) {
        vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                  "Unable to load XML file %s: %s", read_rr_graph_name, result.description());
    }
    is.close();

    if (rr_graph.tool_version && strcmp(rr_graph.tool_version, vtr::VERSION) != 0) {
        VTR_LOG("\n");
        VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s compatability issues may arise\n",
                     rr_graph.tool_version, vtr::VERSION);
        VTR_LOG("\n");
    }
    std::string correct_string = "Generated from arch file ";
    correct_string += get_arch_file_name();
    if (rr_graph.tool_comment && strcmp(rr_graph.tool_comment, correct_string.c_str()) != 0) {
        VTR_LOG("\n");
        VTR_LOG_WARN("This RR graph file is based on %s while your input architecture file is %s compatability issues may arise\n",
                     get_arch_file_name(), rr_graph.tool_comment);
        VTR_LOG("\n");
    }

    /* Decode the graph_type */
    bool is_global_graph = (GRAPH_GLOBAL == graph_type ? true : false);

    /* Compare the grid with the architecture file to ensure consistency. */
    for (auto& g : rr_graph.grid.grid_locs) {
        t_grid_tile& grid_tile = grid[g.x][g.y];
        if (grid_tile.type->index != g.block_type_id) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block_type_id at (%d, %d): arch used ID %d, RR graph used ID %d.", g.x, g.y,
                      (grid_tile.type->index), g.block_type_id);
        }
        if (grid_tile.width_offset != g.width_offset) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's width_offset at (%d, %d)", g.x, g.y);
        }
        if (grid_tile.height_offset != g.height_offset) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's height_offset at (%d, %d)", g.x, g.y);
        }
    }

    /* Compare the block types with the architecture file to ensure consistency. */
    for (auto& block_type : rr_graph.block_types.block_types) {
        auto rr_block_info = device_ctx.physical_tile_types[block_type.id];
        if (strcmp(rr_block_info.name, block_type.name) != 0) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block name: arch uses name %s, RR graph uses name %s",
                      rr_block_info.name, block_type.name);
        }
        if (rr_block_info.width != block_type.width) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block width");
        }
        if (rr_block_info.height != block_type.height) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block height");
        }
        for (size_t i = 0; i < block_type.pin_classes.size(); i++) {
            auto& pin_class = block_type.pin_classes[i];
            auto& rr_class_inf = rr_block_info.class_inf[i];
            auto type = pin_class.type;
            e_pin_type rr_type;
            if (type == uxsd::enum_pin_type::OPEN)
                rr_type = OPEN;
            else if (type == uxsd::enum_pin_type::OUTPUT)
                rr_type = DRIVER;
            else if (type == uxsd::enum_pin_type::INPUT)
                rr_type = RECEIVER;
            else {
                VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                "Valid inputs for class types are \"OPEN\", \"OUTPUT\", and \"INPUT\".");
                rr_type = OPEN;
            }

            if (rr_class_inf.type != rr_type) {
                VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                "Architecture file does not match RR graph's block type");
            }
            if ((size_t)rr_class_inf.num_pins != pin_class.pins.size()) {
                VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                "Incorrect number of pins in %d pin_class in block %s", pin_class.pins.size(), rr_block_info.name);
            }

            for (auto& pin : pin_class.pins) {
                auto index = pin_index_by_num(rr_class_inf, pin.ptc);
                if (index < 0) {
                    VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                    "Architecture file does not match RR graph's block pin list: invalid ptc for pin class");
                }
                if (pin.value != block_type_pin_index_to_name(&rr_block_info, rr_class_inf.pinlist[index])) {
                    VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                    "Architecture file does not match RR graph's block pin list");
                }
            }
        }
    }

    /* Compare the segments with the architecture file to ensure consistency. */
    for (auto& s : rr_graph.segments.segments) {
        if (strcmp(segment_inf[s.id].name.c_str(), s.name) != 0) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                "Architecture file does not match RR graph's segment name: arch uses %s, RR graph uses %s", segment_inf[s.id].name.c_str(), s.name);
        }
        if(s.has_timing){
            if (segment_inf[s.id].Rmetal != s.timing.R_per_meter) {
                VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                "Architecture file does not match RR graph's segment R_per_meter");
            }
            if (segment_inf[s.id].Cmetal != s.timing.C_per_meter) {
                VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                                "Architecture file does not match RR graph's segment C_per_meter");
            }
        }
    }

    VTR_LOG("Starting build routing resource graph...\n");

    /* Copy channels from the uxsdcxx structures. */
    auto& channel = rr_graph.channels.channel;
    t_chan_width nodes_per_chan;
    nodes_per_chan.max = channel.chan_width_max;
    nodes_per_chan.x_min = channel.x_min;
    nodes_per_chan.y_min = channel.y_min;
    nodes_per_chan.x_max = channel.x_max;
    nodes_per_chan.y_max = channel.y_max;
    nodes_per_chan.x_list.resize(grid.height());
    nodes_per_chan.y_list.resize(grid.width());
    for (auto& x : rr_graph.channels.x_lists) {
        if (x.index > nodes_per_chan.x_list.size()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                            "index %d on x_list exceeds x_list size %u",
                            x.index, nodes_per_chan.x_list.size());
        }
        nodes_per_chan.x_list[x.index] = x.info;
    }
    for (auto& y : rr_graph.channels.y_lists) {
        if (y.index > nodes_per_chan.y_list.size()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                            "index %d on y_list exceeds y_list size %u",
                            y.index, nodes_per_chan.y_list.size());
        }
        nodes_per_chan.y_list[y.index] = y.info;
    }

    /* Global routing uses a single longwire track */
    int max_chan_width = (is_global_graph ? 1 : nodes_per_chan.max);
    VTR_ASSERT(max_chan_width > 0);

    /* Copy connection boxes from the uxsdcxx structures. */
    if (rr_graph.has_connection_boxes) {
        auto& connection_boxes = rr_graph.connection_boxes;
        std::vector<ConnectionBox> boxes(connection_boxes.num_boxes);
        for (auto& connection_box : connection_boxes.connection_boxes) {
            VTR_ASSERT(connection_box.id < connection_boxes.num_boxes);
            VTR_ASSERT(boxes.at(connection_box.id).name == "");
            boxes.at(connection_box.id).name = std::string(connection_box.name);
        }
        device_ctx.connection_boxes.reset_boxes(std::make_pair(connection_boxes.x_dim, connection_boxes.y_dim), boxes);
    } else {
        device_ctx.connection_boxes.clear();
    }

    /* Copy switches from the uxsdcxx structures. */
    device_ctx.rr_switch_inf.resize(rr_graph.switches.switches.size());
    for (auto& sw : rr_graph.switches.switches) {
        auto& rr_switch = device_ctx.rr_switch_inf[sw.id];
        bool found_in_arch = false;
        if (sw.name) {
            for (int j = 0; j < device_ctx.num_arch_switches; j++) {
                if (strcmp(device_ctx.arch_switch_inf[j].name, sw.name) == 0) {
                    found_in_arch = true;
                    break;
                }
            }
        }
        if (!found_in_arch) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, "Switch name '%s' not found in architecture\n", sw.name);
        }
        rr_switch.name = vtr::strdup(sw.name);

        SwitchType rr_switch_type;
        if(sw.type == uxsd::enum_switch_type::MUX)
            rr_switch_type = SwitchType::MUX;
        else if(sw.type == uxsd::enum_switch_type::TRISTATE)
            rr_switch_type = SwitchType::TRISTATE;
        else if(sw.type == uxsd::enum_switch_type::PASS_GATE)
            rr_switch_type = SwitchType::PASS_GATE;
        else if(sw.type == uxsd::enum_switch_type::SHORT)
            rr_switch_type = SwitchType::SHORT;
        else if(sw.type == uxsd::enum_switch_type::BUFFER)
            rr_switch_type = SwitchType::BUFFER;
        else
            VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid switch type %d\n", sw.type);
        rr_switch.set_type(rr_switch_type);

        rr_switch.R = sw.timing.R;
        rr_switch.Cin = sw.timing.Cin;
        rr_switch.Cout = sw.timing.Cout;
        rr_switch.Cinternal = sw.timing.Cinternal;
        rr_switch.Tdel = sw.timing.Tdel;
        rr_switch.mux_trans_size = sw.sizing.mux_trans_size;
        rr_switch.buf_size = sw.sizing.buf_size;
    }

    process_nodes_xml(rr_graph);
    process_edges_xml(rr_graph, wire_to_rr_ipin_switch);
    //Partition the rr graph edges for efficient access to configurable/non-configurable
    //edge subsets. Must be done after RR switches have been allocated
    partition_rr_graph_edges(device_ctx);
    process_rr_node_indices(grid);
    init_fan_in(device_ctx.rr_nodes, device_ctx.rr_nodes.size());
    set_cost_indices_xml(rr_graph, is_global_graph, segment_inf.size());
    alloc_and_load_rr_indexed_data(segment_inf, device_ctx.rr_node_indices,
                                   max_chan_width, *wire_to_rr_ipin_switch, base_cost_type);
    process_seg_id_xml(rr_graph);

    device_ctx.chan_width = nodes_per_chan;
    device_ctx.read_rr_graph_filename = std::string(read_rr_graph_name);
    check_rr_graph(graph_type, grid, device_ctx.physical_tile_types);
    device_ctx.connection_boxes.create_sink_back_ref();

    /* Free uxsdcxx memory. */
    uxsd::clear_pools();
    uxsd::clear_strings();
}

/* This function sets the Source pins, sink pins, ipin, and opin
 * to their unique cost index identifier. CHANX and CHANY cost indices are set after the
 * seg_id is read in from the rr graph*/
void set_cost_indices_xml(uxsd::rr_graph& rr_graph, const bool is_global_graph, const int num_seg_types) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    for (size_t inode = 0; inode < device_ctx.rr_nodes.size(); inode++) {
        if (device_ctx.rr_nodes[inode].type() == SOURCE) {
            device_ctx.rr_nodes[inode].set_cost_index(SOURCE_COST_INDEX);
        } else if (device_ctx.rr_nodes[inode].type() == SINK) {
            device_ctx.rr_nodes[inode].set_cost_index(SINK_COST_INDEX);
        } else if (device_ctx.rr_nodes[inode].type() == IPIN) {
            device_ctx.rr_nodes[inode].set_cost_index(IPIN_COST_INDEX);
        } else if (device_ctx.rr_nodes[inode].type() == OPIN) {
            device_ctx.rr_nodes[inode].set_cost_index(OPIN_COST_INDEX);
        }
    }
    /*Go through each rr_node and use the segment ids to set CHANX and CHANY cost index*/
    for (auto& n : rr_graph.rr_nodes.nodes) {
        auto& node = device_ctx.rr_nodes[n.id];
        /*CHANX and CHANY cost index is dependent on the segment id*/
        int seg_id = n.segment.segment_id;
        if (is_global_graph) {
            node.set_cost_index(0);
        } else if (node.type() == CHANX) {
            node.set_cost_index(CHANX_COST_INDEX_START + seg_id);
        } else if (node.type() == CHANY) {
            node.set_cost_index(CHANX_COST_INDEX_START + num_seg_types + seg_id);
        }
    }
}

/*Only CHANX and CHANY components have a segment id. This function
 *reads in the segment id of each node*/
void process_seg_id_xml(uxsd::rr_graph& rr_graph) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    for (auto& n : rr_graph.rr_nodes.nodes) {
        auto& node = device_ctx.rr_nodes[n.id];

        if (node.type() == CHANX || node.type() == CHANY) {
            device_ctx.rr_indexed_data[node.cost_index()].seg_index = n.segment.segment_id;
        } else {
            //-1 for non chanx or chany nodes
            device_ctx.rr_indexed_data[node.cost_index()].seg_index = -1;
        }
    }
}

/* Copy nodes from the uxsdcxx structures. */
void process_nodes_xml(uxsd::rr_graph& rr_graph) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    device_ctx.rr_nodes.resize(rr_graph.rr_nodes.nodes.size());
    device_ctx.connection_boxes.resize_nodes(rr_graph.rr_nodes.nodes.size());

    for (auto& node : rr_graph.rr_nodes.nodes) {
        auto& rr_node = device_ctx.rr_nodes[node.id];
        auto type = node.type;
        if (type == uxsd::enum_node_type::CHANX)
            rr_node.set_type(CHANX);
        else if (type == uxsd::enum_node_type::CHANY)
            rr_node.set_type(CHANY);
        else if (type == uxsd::enum_node_type::SOURCE)
            rr_node.set_type(SOURCE);
        else if (type == uxsd::enum_node_type::SINK)
            rr_node.set_type(SINK);
        else if (type == uxsd::enum_node_type::OPIN)
            rr_node.set_type(OPIN);
        else if (type == uxsd::enum_node_type::IPIN)
            rr_node.set_type(IPIN);
        else
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, "Invalid node type %d.\n", type);

        /* TODO: add connection_box to node in the schema */
        if (rr_node.type() == CHANX || rr_node.type() == CHANY) {
            auto dir = node.direction;
            if (dir == uxsd::enum_node_direction::INC_DIR)
                rr_node.set_direction(INC_DIRECTION);
            else if (dir == uxsd::enum_node_direction::DEC_DIR)
                rr_node.set_direction(DEC_DIRECTION);
            else if (dir == uxsd::enum_node_direction::BI_DIR)
                rr_node.set_direction(BI_DIRECTION);
            else
                VPR_FATAL_ERROR(VPR_ERROR_OTHER, "Invalid node direction %d.\n", dir);
        }

        if (rr_node.type() == IPIN) {
            if (node.has_connection_box) {
                auto& cb = node.connection_box;
                device_ctx.connection_boxes.add_connection_box(node.id, ConnectionBoxId(cb.id), std::make_pair(cb.x, cb.y));
            }
        }

        if (node.has_canonical_loc) {
            auto &cl = node.canonical_loc;
            device_ctx.connection_boxes.add_canonical_loc(node.id, std::make_pair(cl.x, cl.y));
        }

        rr_node.set_capacity(node.capacity);
        rr_node.set_coordinates(node.loc.xlow, node.loc.ylow, node.loc.xhigh, node.loc.yhigh);
        rr_node.set_ptc_num(node.loc.ptc);
        if (rr_node.type() == IPIN || rr_node.type() == OPIN) {
            auto side = node.loc.side;
            if (side == uxsd::enum_loc_side::LEFT)
                rr_node.set_side(LEFT);
            else if (side == uxsd::enum_loc_side::RIGHT)
                rr_node.set_side(RIGHT);
            else if (side == uxsd::enum_loc_side::TOP)
                rr_node.set_side(TOP);
            else if (side == uxsd::enum_loc_side::BOTTOM)
                rr_node.set_side(BOTTOM);
            else
                VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid node side %d.\n", side);
        }
        rr_node.set_rc_index(find_create_rr_rc_data(node.timing.R, node.timing.C));
        rr_node.set_num_edges(0);
        for (auto& meta : node.metadata.metas) {
            vpr::add_rr_node_metadata(node.id, meta.name, meta.value);
        }
    }
}

/* Copy edges from the uxsdcxx structures. */
void process_edges_xml(uxsd::rr_graph& rr_graph, int* wire_to_rr_ipin_switch) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    //count the number of edges and store it in a vector
    std::vector<size_t> num_edges_for_node;
    num_edges_for_node.resize(device_ctx.rr_nodes.size(), 0);
    for (auto& e : rr_graph.rr_edges.edges) {
        if (e.src_node >= device_ctx.rr_nodes.size()) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "source_node %d is larger than rr_nodes.size() %d",
                      e.src_node, device_ctx.rr_nodes.size());
        }
        num_edges_for_node[e.src_node]++;
        device_ctx.rr_nodes[e.src_node].set_num_edges(num_edges_for_node[e.src_node]);
    }
    //reset this vector in order to start count for num edges again
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        if (num_edges_for_node[i] > std::numeric_limits<t_edge_size>::max()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                            "source node %d edge count %d is too high",
                            i, num_edges_for_node[i]);
        }
        device_ctx.rr_nodes[i].set_num_edges(num_edges_for_node[i]);
        num_edges_for_node[i] = 0;
    }
    std::vector<int> count_for_wire_to_ipin_switches;
    count_for_wire_to_ipin_switches.resize(device_ctx.rr_nodes.size(), 0);
    //first is index, second is count
    std::pair<int, int> most_frequent_switch(-1, 0);

    for (auto& e : rr_graph.rr_edges.edges) {
        if (e.sink_node >= device_ctx.rr_nodes.size()) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "sink_node %d is larger than rr_nodes.size() %d",
                      e.sink_node, device_ctx.rr_nodes.size());
        }
        if (e.switch_id >= device_ctx.rr_nodes.size()) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "switch_id %d is larger than num_rr_switches %d",
                      e.switch_id, device_ctx.rr_nodes.size());
        }
        /*Keeps track of the number of the specific type of switch that connects a wire to an ipin
         * use the pair data structure to keep the maximum*/
        if (device_ctx.rr_nodes[e.src_node].type() == CHANX || device_ctx.rr_nodes[e.src_node].type() == CHANY) {
            if (device_ctx.rr_nodes[e.sink_node].type() == IPIN) {
                count_for_wire_to_ipin_switches[e.switch_id]++;
                if (count_for_wire_to_ipin_switches[e.switch_id] > most_frequent_switch.second) {
                    most_frequent_switch.first = e.switch_id;
                    most_frequent_switch.second = count_for_wire_to_ipin_switches[e.switch_id];
                }
            }
        }
        //set edge in correct rr_node data structure
        device_ctx.rr_nodes[e.src_node].set_edge_sink_node(num_edges_for_node[e.src_node], e.sink_node);
        device_ctx.rr_nodes[e.src_node].set_edge_switch(num_edges_for_node[e.src_node], e.switch_id);

        // Read the metadata for the edge
        for (auto& meta : e.metadata.metas) {
            vpr::add_rr_edge_metadata(e.src_node, e.sink_node, e.switch_id, meta.name, meta.value);
        }
        num_edges_for_node[e.src_node]++;
    }
    *wire_to_rr_ipin_switch = most_frequent_switch.first;
    num_edges_for_node.clear();
    count_for_wire_to_ipin_switches.clear();
}

/*Allocates and load the rr_node look up table. SINK and SOURCE, IPIN and OPIN
 *share the same look up table. CHANX and CHANY have individual look ups */
void process_rr_node_indices(const DeviceGrid& grid) {
    auto& device_ctx = g_vpr_ctx.mutable_device();

    /* Alloc the lookup table */

    auto& indices = device_ctx.rr_node_indices;

    indices.resize(NUM_RR_TYPES);

    typedef struct max_ptc {
        short chanx_max_ptc = 0;
        short chany_max_ptc = 0;
    } t_max_ptc;

    /*
     * Local multi-dimensional vector to hold max_ptc for every coordinate.
     * It has same height and width as CHANY and CHANX are inverted
     */
    vtr::Matrix<t_max_ptc> coordinates_max_ptc; /* [x][y] */
    size_t max_coord_size = std::max(grid.width(), grid.height());
    coordinates_max_ptc.resize({max_coord_size, max_coord_size}, t_max_ptc());

    /* Alloc the lookup table */
    for (t_rr_type rr_type : RR_TYPES) {
        if (rr_type == CHANX) {
            indices[rr_type].resize(grid.height());
            for (size_t y = 0; y < grid.height(); ++y) {
                indices[rr_type][y].resize(grid.width());
                for (size_t x = 0; x < grid.width(); ++x) {
                    indices[rr_type][y][x].resize(NUM_SIDES);
                }
            }
        } else {
            indices[rr_type].resize(grid.width());
            for (size_t x = 0; x < grid.width(); ++x) {
                indices[rr_type][x].resize(grid.height());
                for (size_t y = 0; y < grid.height(); ++y) {
                    indices[rr_type][x][y].resize(NUM_SIDES);
                }
            }
        }
    }

    /*
     * Add the correct node into the vector
     * For CHANX and CHANY no node is added yet, but the maximum ptc is counted for each
     * x/y location. This is needed later to add the correct node corresponding to CHANX
     * and CHANY.
     *
     * Note that CHANX and CHANY 's x and y are swapped due to the chan and seg convention.
     */
    for (size_t inode = 0; inode < device_ctx.rr_nodes.size(); inode++) {
        auto& node = device_ctx.rr_nodes[inode];
        if (node.type() == SOURCE || node.type() == SINK) {
            for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                    if (node.type() == SOURCE) {
                        indices[SOURCE][ix][iy][0].push_back(inode);
                        indices[SINK][ix][iy][0].push_back(OPEN);
                    } else {
                        VTR_ASSERT(node.type() == SINK);
                        indices[SINK][ix][iy][0].push_back(inode);
                        indices[SOURCE][ix][iy][0].push_back(OPEN);
                    }
                }
            }
        } else if (node.type() == IPIN || node.type() == OPIN) {
            for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                    if (node.type() == OPIN) {
                        indices[OPIN][ix][iy][node.side()].push_back(inode);
                        indices[IPIN][ix][iy][node.side()].push_back(OPEN);
                    } else {
                        VTR_ASSERT(node.type() == IPIN);
                        indices[IPIN][ix][iy][node.side()].push_back(inode);
                        indices[OPIN][ix][iy][node.side()].push_back(OPEN);
                    }
                }
            }
        } else if (node.type() == CHANX) {
            for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                    coordinates_max_ptc[iy][ix].chanx_max_ptc = std::max(coordinates_max_ptc[iy][ix].chanx_max_ptc, node.ptc_num());
                }
            }
        } else if (node.type() == CHANY) {
            for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                    coordinates_max_ptc[ix][iy].chany_max_ptc = std::max(coordinates_max_ptc[ix][iy].chany_max_ptc, node.ptc_num());
                }
            }
        }
    }

    /* Alloc the lookup table */
    for (t_rr_type rr_type : RR_TYPES) {
        if (rr_type == CHANX) {
            for (size_t y = 0; y < grid.height(); ++y) {
                for (size_t x = 0; x < grid.width(); ++x) {
                    indices[CHANX][y][x][0].resize(coordinates_max_ptc[y][x].chanx_max_ptc + 1, OPEN);
                }
            }
        } else if (rr_type == CHANY) {
            for (size_t x = 0; x < grid.width(); ++x) {
                for (size_t y = 0; y < grid.height(); ++y) {
                    indices[CHANY][x][y][0].resize(coordinates_max_ptc[x][y].chany_max_ptc + 1, OPEN);
                }
            }
        }
    }

    int count;
    /* CHANX and CHANY need to reevaluated with its ptc num as the correct index*/
    for (size_t inode = 0; inode < device_ctx.rr_nodes.size(); inode++) {
        auto& node = device_ctx.rr_nodes[inode];
        if (node.type() == CHANX) {
            for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                    count = node.ptc_num();
                    if (count >= int(indices[CHANX][iy][ix][0].size())) {
                        VPR_FATAL_ERROR(VPR_ERROR_ROUTE,
                                        "Ptc index %d for CHANX (%d, %d) is out of bounds, size = %zu",
                                        count, ix, iy, indices[CHANX][iy][ix][0].size());
                    }
                    indices[CHANX][iy][ix][0][count] = inode;
                }
            }
        } else if (node.type() == CHANY) {
            for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
                for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
                    count = node.ptc_num();
                    if (count >= int(indices[CHANY][ix][iy][0].size())) {
                        VPR_FATAL_ERROR(VPR_ERROR_ROUTE,
                                        "Ptc index %d for CHANY (%d, %d) is out of bounds, size = %zu",
                                        count, ix, iy, indices[CHANY][ix][iy][0].size());
                    }
                    indices[CHANY][ix][iy][0][count] = inode;
                }
            }
        }
    }

    //Copy the SOURCE/SINK nodes to all offset positions for blocks with width > 1 and/or height > 1
    // This ensures that look-ups on non-root locations will still find the correct SOURCE/SINK
    for (size_t x = 0; x < grid.width(); x++) {
        for (size_t y = 0; y < grid.height(); y++) {
            int width_offset = grid[x][y].width_offset;
            int height_offset = grid[x][y].height_offset;
            if (width_offset != 0 || height_offset != 0) {
                int root_x = x - width_offset;
                int root_y = y - height_offset;

                indices[SOURCE][x][y] = indices[SOURCE][root_x][root_y];
                indices[SINK][x][y] = indices[SINK][root_x][root_y];
            }
        }
    }

    device_ctx.rr_node_indices = indices;
}

/**
 * Load a Cap'n Proto rr_graph.
 */
void load_rr_file_capnp(const t_graph_type graph_type,
                        const DeviceGrid& grid,
                        const std::vector<t_segment_inf>& segment_inf,
                        const enum e_base_cost_type base_cost_type,
                        int* wire_to_rr_ipin_switch,
                        const char* read_rr_graph_name) {
    auto& device_ctx = g_vpr_ctx.mutable_device();

    vtr::ScopedStartFinishTimer timer("Loading routing resource graph");
    MmapFile f(read_rr_graph_name);
    /* Increase reader limit to 1G words. */
    ::capnp::ReaderOptions opts = ::capnp::ReaderOptions();
    opts.traversalLimitInWords = 1024 * 1024 * 1024;
    ::capnp::FlatArrayMessageReader reader(f.getData(), opts);
    auto rr_graph = reader.getRoot<ucap::RrGraph>();

    const char* tool_version = rr_graph.getToolVersion().cStr();
    if (tool_version && strcmp(tool_version, vtr::VERSION) != 0) {
        VTR_LOG("\n");
        VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s compatability issues may arise\n", vtr::VERSION, tool_version);
        VTR_LOG("\n");
    }
    const char* tool_comment = rr_graph.getToolComment().cStr();
    std::string correct_string = "Generated from arch file ";
    correct_string += get_arch_file_name();
    if (tool_comment && strcmp(tool_comment, correct_string.c_str()) != 0) {
        VTR_LOG("\n");
        VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s compatability issues may arise\n", vtr::VERSION, tool_version);
        VTR_LOG("\n");
    }

    /* Decode the graph_type */
    bool is_global_graph = (GRAPH_GLOBAL == graph_type ? true : false);

    /* Compare the grid with the architecture file to ensure consistency. */
    auto grid_locs = rr_graph.getGrid().getGridLocs();
    for (auto grid_loc : grid_locs) {
        int x = grid_loc.getX();
        int y = grid_loc.getY();
        int block_type_id = grid_loc.getBlockTypeId();
        int width_offset = grid_loc.getWidthOffset();
        int height_offset = grid_loc.getHeightOffset();
        t_grid_tile& grid_tile = grid[x][y];
        if (grid_tile.type->index != block_type_id) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block_type_id at (%d, %d): arch used ID %d, RR graph used ID %d.",
                      x, y, (grid_tile.type->index), block_type_id);
        }
        if (grid_tile.width_offset != width_offset) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's width_offset at (%d, %d)", x, y);
        }
        if (grid_tile.height_offset != height_offset) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's height_offset at (%d, %d)", x, y);
        }
    }

    /* Compare the block types with the architecture file to ensure consistency. */
    auto block_types_parent = rr_graph.getBlockTypes();
    auto block_types = block_types_parent.getBlockTypes();
    for (auto block_type : block_types) {
        int id = block_type.getId();
        const char* name = block_type.getName().cStr();
        auto arch_block_type = device_ctx.physical_tile_types[id];
        if (strcmp(arch_block_type.name, name) != 0) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block name: arch uses name %s, RR graph uses name %s",
                      arch_block_type.name, name);
        }
        if (arch_block_type.width != block_type.getWidth()) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block width");
        }
        if (arch_block_type.height != block_type.getHeight()) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's block height");
        }

        auto pin_classes = block_type.getPinClasses();
        for (unsigned int i = 0; i < pin_classes.size(); i++) {
            auto pin_class = pin_classes[i];
            auto& arch_pin_class = arch_block_type.class_inf[i];
            auto type = pin_class.getType();
            e_pin_type rr_type;
            if (type == ucap::PinType::OPEN)
                rr_type = OPEN;
            else if (type == ucap::PinType::OUTPUT)
                rr_type = DRIVER;
            else if (type == ucap::PinType::INPUT)
                rr_type = RECEIVER;
            else
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid pin class type %d.\n", type);
            if (arch_pin_class.type != rr_type) {
                vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                          "Architecture file does not match RR graph's block type");
            }
            auto pins = pin_class.getPins();
            if ((unsigned int)arch_pin_class.num_pins != pins.size()) {
                vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                          "Incorrect number of pins in pin_class %d in block %s", i, arch_block_type.name);
            }
            for (auto pin : pins) {
                auto index = pin_index_by_num(arch_pin_class, pin.getPtc());
                if (index < 0) {
                    vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                              "Architecture file does not match RR graph's block pin list: invalid ptc for pin class");
                }
                const char* value = pin.getValue().cStr();
                std::string arch_pin_name = block_type_pin_index_to_name(&arch_block_type, arch_pin_class.pinlist[index]);
                if (strcmp(value, arch_pin_name.c_str()) != 0) {
                    vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                              "Architecture file does not match RR graph's block pin list");
                }
            }
        }
    }

    /* Compare segments with the architecture file to ensure consistency. */
    auto segments_parent = rr_graph.getSegments();
    auto segments = segments_parent.getSegments();
    for (auto segment : segments) {
        auto& rr_segment = segment_inf[segment.getId()];
        const char* name = segment.getName().cStr();
        if (strcmp(name, rr_segment.name.c_str()) != 0) {
            vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                      "Architecture file does not match RR graph's segment name: arch uses %s, RR graph uses %s",
                      rr_segment.name.c_str(), name);
        }
        if(segment.hasTiming()){
            auto timing = segment.getTiming();
            if (rr_segment.Rmetal != timing.getRPerMeter()) {
                vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                          "Architecture file does not match RR graph's segment R_per_meter");
            }
            if (rr_segment.Cmetal != timing.getCPerMeter()) {
                vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                          "Architecture file does not match RR graph's segment C_per_meter");
            }
        }
    }

    VTR_LOG("Starting build routing resource graph...\n");

    /* Copy channels from the Cap'n Proto structures. */
    auto channels = rr_graph.getChannels();
    auto channel = channels.getChannel();
    t_chan_width nodes_per_chan;
    nodes_per_chan.max = channel.getChanWidthMax();
    nodes_per_chan.x_min = channel.getXMin();
    nodes_per_chan.y_min = channel.getYMin();
    nodes_per_chan.x_max = channel.getXMax();
    nodes_per_chan.y_max = channel.getYMax();
    nodes_per_chan.x_list.resize(grid.height());
    nodes_per_chan.y_list.resize(grid.width());
    auto x_lists = channels.getXLists();
    for (auto x_list : x_lists) {
        size_t index = x_list.getIndex();
        if (index > nodes_per_chan.x_list.size()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                      "index %d on x_list exceeds x_list size %u",
                      index, nodes_per_chan.x_list.size());
        }
        nodes_per_chan.x_list[index] = x_list.getInfo();
    }
    auto y_lists = channels.getYLists();
    for (auto y_list : y_lists) {
        size_t index = y_list.getIndex();
        if (index > nodes_per_chan.y_list.size()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                      "index %d on y_list exceeds y_list size %u",
                      index, nodes_per_chan.y_list.size());
        }
        nodes_per_chan.y_list[index] = y_list.getInfo();
    }

    /* Global routing uses a single longwire track */
    int max_chan_width = (is_global_graph ? 1 : nodes_per_chan.max);
    VTR_ASSERT(max_chan_width > 0);

    /* Copy connection boxes from the Cap'n Proto structures. */
    if (rr_graph.hasConnectionBoxes()) {
        auto connection_boxes_parent = rr_graph.getConnectionBoxes();
        auto connection_boxes = connection_boxes_parent.getConnectionBoxes();
        int x_dim = connection_boxes_parent.getXDim();
        int y_dim = connection_boxes_parent.getYDim();
        unsigned int num_boxes = connection_boxes_parent.getNumBoxes();
        std::vector<ConnectionBox> boxes(num_boxes);
        for (auto connection_box : connection_boxes) {
            unsigned int id = connection_box.getId();
            const char* name = connection_box.getName().cStr();
            VTR_ASSERT(id < num_boxes);
            VTR_ASSERT(boxes.at(id).name == "");
            boxes.at(id).name = std::string(name);
        }
        device_ctx.connection_boxes.reset_boxes(std::make_pair(x_dim, y_dim), boxes);
    } else {
        device_ctx.connection_boxes.clear();
    }

    /* Copy switches from the uxsdcxx structures. */
    auto switches_parent = rr_graph.getSwitches();
    auto switches = switches_parent.getSwitches();
    device_ctx.rr_switch_inf.resize(switches.size());
    for (auto switch_ : switches) {
        int id = switch_.getId();
        auto& rr_switch = device_ctx.rr_switch_inf[id];
        const char* name = switch_.getName().cStr();
        bool found_in_arch = false;
        if (name) {
            for (int j = 0; j < device_ctx.num_arch_switches; j++) {
                if (strcmp(device_ctx.arch_switch_inf[j].name, name) == 0) {
                    found_in_arch = true;
                    break;
                }
            }
        }
        if (!found_in_arch)
            VPR_THROW(VPR_ERROR_ROUTE, "Switch name '%s' not found in architecture\n", name);
        ucap::SwitchType type = switch_.getType();
        if (type == ucap::SwitchType::MUX)
            rr_switch.set_type(SwitchType::MUX);
        else if (type == ucap::SwitchType::TRISTATE)
            rr_switch.set_type(SwitchType::TRISTATE);
        else if (type == ucap::SwitchType::PASS_GATE)
            rr_switch.set_type(SwitchType::PASS_GATE);
        else if (type == ucap::SwitchType::SHORT)
            rr_switch.set_type(SwitchType::SHORT);
        else if (type == ucap::SwitchType::BUFFER)
            rr_switch.set_type(SwitchType::BUFFER);
        else
            VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid switch type %d\n", type);
        rr_switch.name = vtr::strdup(switch_.getName().cStr());
        auto timing = switch_.getTiming();
        rr_switch.R = timing.getR();
        rr_switch.Cin = timing.getCin();
        rr_switch.Cout = timing.getCout();
        rr_switch.Cinternal = timing.getCinternal();
        rr_switch.Tdel = timing.getTdel();
        auto sizing = switch_.getSizing();
        rr_switch.mux_trans_size = sizing.getMuxTransSize();
        rr_switch.buf_size = sizing.getBufSize();
    }

    /* Copy nodes and edges, set up routing data structures. */
    process_nodes_capnp(rr_graph);
    process_edges_capnp(rr_graph, wire_to_rr_ipin_switch);

    //Partition the rr graph edges for efficient access to configurable/non-configurable
    //edge subsets. Must be done after RR switches have been allocated.
    partition_rr_graph_edges(device_ctx);
    process_rr_node_indices(grid);
    init_fan_in(device_ctx.rr_nodes, device_ctx.rr_nodes.size());
    set_cost_indices_capnp(rr_graph, is_global_graph, segment_inf.size());
    alloc_and_load_rr_indexed_data(segment_inf, device_ctx.rr_node_indices,
                                   max_chan_width, *wire_to_rr_ipin_switch, base_cost_type);
    process_seg_id_capnp(rr_graph);

    device_ctx.chan_width = nodes_per_chan;
    device_ctx.read_rr_graph_filename = std::string(read_rr_graph_name);
    check_rr_graph(graph_type, grid, device_ctx.physical_tile_types);
    device_ctx.connection_boxes.create_sink_back_ref();
}

/* Read in rr_nodes from a Cap'n Proto message reader. */
void process_nodes_capnp(ucap::RrGraph::Reader& rr_graph) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    auto rr_nodes = rr_graph.getRrNodes();
    auto nodes = rr_nodes.getNodes();
    device_ctx.rr_nodes.resize(nodes.size());
    device_ctx.connection_boxes.resize_nodes(nodes.size());
    for (auto node : nodes) {
        int id = node.getId();
        auto& rr_node = device_ctx.rr_nodes[id];
        auto type = node.getType();
        if (type == ucap::NodeType::CHANX)
            rr_node.set_type(CHANX);
        else if (type == ucap::NodeType::CHANY)
            rr_node.set_type(CHANY);
        else if (type == ucap::NodeType::SOURCE)
            rr_node.set_type(SOURCE);
        else if (type == ucap::NodeType::SINK)
            rr_node.set_type(SINK);
        else if (type == ucap::NodeType::OPIN)
            rr_node.set_type(OPIN);
        else if (type == ucap::NodeType::IPIN)
            rr_node.set_type(IPIN);
        else
            VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid node type %d.\n", type);
        if (rr_node.type() == CHANX || rr_node.type() == CHANY) {
            auto direction = node.getDirection();
            if (direction == ucap::NodeDirection::INC_DIR)
                rr_node.set_direction(INC_DIRECTION);
            else if (direction == ucap::NodeDirection::DEC_DIR)
                rr_node.set_direction(DEC_DIRECTION);
            else if (direction == ucap::NodeDirection::BI_DIR)
                rr_node.set_direction(BI_DIRECTION);
            else
                VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid node direction %d.\n", direction);
        }

        if (rr_node.type() == IPIN) {
            if (node.hasConnectionBox()) {
                auto cb = node.getConnectionBox();
                device_ctx.connection_boxes.add_connection_box(id, ConnectionBoxId(cb.getId()), std::make_pair(cb.getX(), cb.getY()));
            }
        }

        if (node.hasCanonicalLoc()) {
            auto cl = node.getCanonicalLoc();
            device_ctx.connection_boxes.add_canonical_loc(id, std::make_pair(cl.getX(), cl.getY()));
        }

        rr_node.set_capacity(node.getCapacity());
        auto loc = node.getLoc();
        rr_node.set_coordinates(loc.getXlow(), loc.getYlow(), loc.getXhigh(), loc.getYhigh());
        rr_node.set_ptc_num(loc.getPtc());
        if (rr_node.type() == IPIN || rr_node.type() == OPIN) {
            auto side = loc.getSide();
            if (side == ucap::LocSide::LEFT)
                rr_node.set_side(LEFT);
            else if (side == ucap::LocSide::RIGHT)
                rr_node.set_side(RIGHT);
            else if (side == ucap::LocSide::TOP)
                rr_node.set_side(TOP);
            else if (side == ucap::LocSide::BOTTOM)
                rr_node.set_side(BOTTOM);
            else
                VPR_FATAL_ERROR(VPR_ERROR_ROUTE, "Invalid node side %d.\n", side);
        }
        auto timing = node.getTiming();
        rr_node.set_rc_index(find_create_rr_rc_data(timing.getR(), timing.getC()));
        rr_node.set_num_edges(0);
        auto metadata = node.getMetadata();
        auto metas = metadata.getMetas();
        for (auto meta : metas) {
            vpr::add_rr_node_metadata(id, meta.getName(), meta.getValue());
        }
    }
}

void process_edges_capnp(ucap::RrGraph::Reader& rr_graph, int* wire_to_rr_ipin_switch) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    auto rr_edges = rr_graph.getRrEdges();
    auto edges = rr_edges.getEdges();
    auto num_rr_nodes = device_ctx.rr_nodes.size();
    //count the number of edges and store it in a vector
    std::vector<size_t> num_edges_for_node;
    num_edges_for_node.resize(num_rr_nodes, 0);

    for (auto edge : edges) {
        size_t src_node_id = edge.getSrcNode();
        if (src_node_id > num_rr_nodes)
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                            "src_node %d is larger than rr_nodes.size() %d", src_node_id, num_rr_nodes);
        num_edges_for_node[src_node_id]++;
        device_ctx.rr_nodes[src_node_id].set_num_edges(num_edges_for_node[src_node_id]);
    }

    //reset this vector in order to start count for num edges again
    for (size_t i = 0; i < num_rr_nodes; i++) {
        if (num_edges_for_node[i] > std::numeric_limits<t_edge_size>::max()) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER,
                            "source node %d edge count %d is too high",
                            i, num_edges_for_node[i]);
        }
        device_ctx.rr_nodes[i].set_num_edges(num_edges_for_node[i]);
        num_edges_for_node[i] = 0;
    }
    std::vector<int> count_for_wire_to_ipin_switches;
    count_for_wire_to_ipin_switches.resize(num_rr_nodes, 0);
    //first is index, second is count
    std::pair<int, int> most_frequent_switch(-1, 0);

    for (auto edge : edges) {
        size_t src_node_id = edge.getSrcNode();
        size_t sink_node_id = edge.getSinkNode();
        size_t switch_id = edge.getSwitchId();
        if (sink_node_id >= num_rr_nodes) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, __FILE__, __LINE__,
                            "sink_node %d is larger than rr_nodes.size() %d", sink_node_id, num_rr_nodes);
        }
        if (switch_id >= num_rr_nodes) {
            VPR_FATAL_ERROR(VPR_ERROR_OTHER, __FILE__, __LINE__,
                            "sink_node %d is larger than rr_nodes.size() %d", switch_id, num_rr_nodes);
        }
        /* Keeps track of the number of a specific type of switch that connects
         * a wire to an ipin. Uses the pair data structure to keep the maximum. */
        auto& src_node = device_ctx.rr_nodes[src_node_id];
        if (src_node.type() == CHANX || src_node.type() == CHANY) {
            auto& sink_node = device_ctx.rr_nodes[sink_node_id];
            if (sink_node.type() == IPIN) {
                count_for_wire_to_ipin_switches[switch_id]++;
                if (count_for_wire_to_ipin_switches[switch_id] > most_frequent_switch.second) {
                    most_frequent_switch.first = switch_id;
                    most_frequent_switch.second = count_for_wire_to_ipin_switches[switch_id];
                }
            }
        }
        //set edge in correct rr_node data structure
        src_node.set_edge_sink_node(num_edges_for_node[src_node_id], sink_node_id);
        src_node.set_edge_switch(num_edges_for_node[src_node_id], switch_id);
        // Read the metadata for the edge
        auto metadata = edge.getMetadata();
        auto metas = metadata.getMetas();
        for (auto meta : metas) {
            vpr::add_rr_edge_metadata(src_node_id, sink_node_id, switch_id, meta.getName(), meta.getValue());
        }
        num_edges_for_node[src_node_id]++;
    }
    *wire_to_rr_ipin_switch = most_frequent_switch.first;
    num_edges_for_node.clear();
    count_for_wire_to_ipin_switches.clear();
}

void process_seg_id_capnp(ucap::RrGraph::Reader& rr_graph) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    auto nodes = rr_graph.getRrNodes().getNodes();
    for (auto node : nodes) {
        auto& rr_node = device_ctx.rr_nodes[node.getId()];
        if (rr_node.type() == CHANX || rr_node.type() == CHANY) {
            int segment_id = node.getSegment().getSegmentId();
            device_ctx.rr_indexed_data[rr_node.cost_index()].seg_index = segment_id;
        } else {
            device_ctx.rr_indexed_data[rr_node.cost_index()].seg_index = -1;
        }
    }
}

/* This function sets the Source pins, sink pins, ipin, and opin
 * to their unique cost index identifier. CHANX and CHANY cost indices are set
 * after the seg_id is read in from the rr graph. */
void set_cost_indices_capnp(ucap::RrGraph::Reader& rr_graph, const bool is_global_graph, const int num_seg_types) {
    auto& device_ctx = g_vpr_ctx.mutable_device();
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        auto& rr_node = device_ctx.rr_nodes[i];
        if (rr_node.type() == SOURCE) {
            rr_node.set_cost_index(SOURCE_COST_INDEX);
        } else if (rr_node.type() == SINK) {
            rr_node.set_cost_index(SINK_COST_INDEX);
        } else if (rr_node.type() == IPIN) {
            rr_node.set_cost_index(IPIN_COST_INDEX);
        } else if (rr_node.type() == OPIN) {
            rr_node.set_cost_index(OPIN_COST_INDEX);
        }
    }
    /*Go through each rr_node and use the segment ids to set CHANX and CHANY cost index */
    auto nodes = rr_graph.getRrNodes().getNodes();
    for (auto node : nodes) {
        auto& rr_node = device_ctx.rr_nodes[node.getId()];
        /* CHANX and CHANY cost index is dependent on the segment id */
        int seg_id = node.getSegment().getSegmentId();
        if (is_global_graph) {
            rr_node.set_cost_index(0);
        } else if (rr_node.type() == CHANX) {
            rr_node.set_cost_index(CHANX_COST_INDEX_START + seg_id);
        } else if (rr_node.type() == CHANY) {
            rr_node.set_cost_index(CHANX_COST_INDEX_START + num_seg_types + seg_id);
        }
    }
}

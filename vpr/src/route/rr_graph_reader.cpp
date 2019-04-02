/*This function loads in a routing resource graph written in xml format
 * into vpr when the option --read_rr_graph <file name> is specified.
 * When it is not specified the build_rr_graph function is then called.
 * This is done using the libxml2 library. This is useful
 * when specific routing resources should remain constant or when
 * some information left out in the architecture can be specified
 * in the routing resource graph. The routing resource graph file is
 * contained in a <rr_graph> tag. Its subtags describe the rr graph's
 * various features such as nodes, edges, and segments. Information such
 * as blocks, grids, and segments are verified with the architecture
 * to ensure it matches. An error will be thrown if any feature does not match.
 * Other elements such as edges, nodes, and switches
 * are overwritten by the rr graph file if one is specified. If an optional
 * identifier such as capacitance is not specified, it is set to 0. */

#include <algorithm>
#include <cstring>
#include <ctime>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stack>
#include <unordered_map>
#include <utility>
#include <vector>

#include "vtr_version.h"
#include "vtr_assert.h"
#include "vtr_util.h"
#include "vtr_memory.h"
#include "vtr_matrix.h"
#include "vtr_math.h"
#include "vtr_log.h"
#include "vtr_time.h"

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

#include <libxml/parser.h>

/********************* Subroutines local to this module *******************/
void load_rr_file(const char *name);

void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs);
void on_end_element(void *ctx, const xmlChar *name);
void on_characters(void *ctx, const xmlChar *ch, int len);

void consume_channels(void);
void consume_switches(void);
void consume_segments(void);
void consume_block_types(void);
void consume_grid(void);
void consume_rr_nodes(void);
void consume_rr_edges(void);
void consume_channel(void);
void consume_x_list(void);
void consume_y_list(void);
void consume_switch(void);
void consume_switch_timing(void);
void consume_switch_sizing(void);
void consume_segment(void);
void consume_segment_timing(void);
void consume_block_type(void);
void consume_pin_class(void);
void consume_pin(void);
void consume_grid_loc(void);
void consume_node(void);
void consume_node_loc(void);
void consume_node_timing(void);
void consume_node_segment(void);
void consume_node_metadata(void);
void consume_meta(void);
void consume_edge(void);
void consume_edge_metadata(void);

void process_edges(int *wire_to_rr_ipin_switch);
void process_rr_node_indices(const DeviceGrid& grid);
void set_cost_indices(bool is_global_graph, const int num_seg_types);
void process_seg_id();

/********************* Global variables for this module *******************/
/* libxml2 interface */
static xmlSAXHandler sax_handler = {};

/* We need to build the current <meta> node piece by piece here. For edge metadata,
 information about the current edge is also required. */
static std::string current_meta_name;
static enum {NODE, EDGE} current_meta_place;
static struct {int src_id; int sink_id; int switch_id;} current_edge;

/* The <edge> handler(consume_node()) tracks the most frequently appearing switch that
 * connects a CHANX/CHANY node to a IPIN node. It is then assigned to *wire_to_rr_ipin_switch. */
int *count_for_wire_to_ipin_switches = NULL;
struct {int id; int count;} most_frequent_switch = {-1, 0};

/* current_node_id is kept because we need to build a map from node IDs to segment IDs
 * and t_rr_node does not hold IDs.
 * !! Also note that it's assumed that nodes appear in ID order and no ID gaps occur. */
static int current_node_id;

/* Pointers to arguments to load_rr_file: we need to access them from SAX handlers. */
static t_chan_width *chan_width;
static const DeviceGrid *g_grid;

/* Map tag names to ints. This helps us build a lookup table of function pointers instead of a hashmap,
 * and it also enables us to use an array of ints instead of a std::stack of std::strings as the parser stack. */
enum tag_type : int {
	T_RR_GRAPH = 0, T_CHANNELS, T_SWITCHES, T_SEGMENTS,
	T_BLOCK_TYPES, T_GRID, T_RR_NODES, T_RR_EDGES, T_CHANNEL,
	T_X_LIST, T_Y_LIST, T_SWITCH, T_TIMING, T_SIZING, T_SEGMENT,
	T_BLOCK_TYPE, T_PIN_CLASS, T_PIN, T_GRID_LOC, T_NODE,
	T_EDGE, T_METADATA, T_META, T_LOC,
};
enum { NUM_TAG_TYPES = 24 };

/* To look up the tag type from the tag name, a perfect hash function from gperf is used.
 * To generate a new one, update tag_gperf_input.txt in this directory and
 * run the command `gperf -t --enum tag_gperf_input.txt`.
 *
 * Note that the code from gperf is reformatted, the wordlist is taken outside as a global variable,
 * prefixed to not clash with attribute lookup, and the lookup function is changed to take just the
 * const char * and return a tag_type. Furthermore, the length check is removed, since most of the
 * incoming strings are known and an unknown string would be recognized in the strcmp check anyway.
 * In case of regeneration, it might be easier to keep the lookup function. */
struct t_tag_lookup {const char *name; tag_type value;};
static t_tag_lookup tag_wordlist[] = {
	{""}, {""}, {""},
	{"pin", T_PIN},
	{"edge", T_EDGE},
	{""},
	{"loc", T_LOC},
	{""},
	{"rr_edges", T_RR_EDGES},
	{"pin_class", T_PIN_CLASS},
	{""},
	{"switch", T_SWITCH},
	{""},
	{"switches", T_SWITCHES},
	{"node", T_NODE},
	{""},
	{"timing", T_TIMING},
	{""},
	{"rr_nodes", T_RR_NODES},
	{""}, {""},
	{"sizing", T_SIZING},
	{"segment", T_SEGMENT},
	{"segments", T_SEGMENTS},
	{""}, {""},
	{"y_list", T_Y_LIST},
	{""},
	{"rr_graph", T_RR_GRAPH},
	{"grid", T_GRID},
	{"block_type", T_BLOCK_TYPE},
	{"block_types", T_BLOCK_TYPES},
	{""},
	{"grid_loc", T_GRID_LOC},
	{""}, {""},
	{"x_list", T_X_LIST},
	{"channel", T_CHANNEL},
	{"channels", T_CHANNELS},
	{"meta", T_META},
	{""}, {""}, {""},
	{"metadata", T_METADATA}
};

static unsigned char tag_asso_values[] = {
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 0, 44, 25, 0, 20,
	 5, 0, 44, 20, 44, 10, 44, 44, 3, 10,
	10, 44, 0, 44, 0, 5, 0, 44, 44, 44,
	20, 10, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
	44, 44, 44, 44, 44, 44
};

static inline unsigned int tag_hash(const char *str, size_t len){
	unsigned int hval = len;
	switch (hval){
	default:
		hval += tag_asso_values[(unsigned char)str[3]];
	/*FALLTHROUGH*/
	case 3:
	case 2:
	case 1:
		hval += tag_asso_values[(unsigned char)str[0]];
		break;
	}
	return hval;
}

static inline tag_type lookup_tag(const char *str){
	enum {
		TOTAL_KEYWORDS = 24,
		MIN_WORD_LENGTH = 3,
		MAX_WORD_LENGTH = 11,
		MIN_HASH_VALUE = 3,
		MAX_HASH_VALUE = 43
	};
	int len = std::strlen(str);
	unsigned int key = tag_hash(str, len);
	if (key <= MAX_HASH_VALUE){
		const char *s = tag_wordlist[key].name;
		if(strcmp(str, s) == 0)
			return tag_wordlist[key].value;
	}
	vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Unrecognized tag <%s>.", str);
}
/* End of gperf code. */

/* The parser stack to keep the current path of tags.
 * It can have a static size, because there is no recursive nesting in the file format. */
static tag_type parser_stack[64];
static int parser_stack_top = -1;

/* The lookup table. It maps the previous tag and current tag to the handler function.
 * It is initialized using a class because C++ doesn't like array initialization using enums. */
class ParseTableClass {
public:
	ParseTableClass(){
		table[T_RR_GRAPH][T_CHANNELS] = consume_channels;
		table[T_RR_GRAPH][T_SWITCHES] = consume_switches;
		table[T_RR_GRAPH][T_SEGMENTS] = consume_segments;
		table[T_RR_GRAPH][T_BLOCK_TYPES] = consume_block_types;
		table[T_RR_GRAPH][T_GRID] = consume_grid;
		table[T_RR_GRAPH][T_RR_NODES] = consume_rr_nodes;
		table[T_RR_GRAPH][T_RR_EDGES] = consume_rr_edges;
		table[T_CHANNELS][T_CHANNEL] = consume_channel;
		table[T_CHANNELS][T_X_LIST] = consume_x_list;
		table[T_CHANNELS][T_Y_LIST] = consume_y_list;
		table[T_SWITCHES][T_SWITCH] = consume_switch;
		table[T_SWITCH][T_TIMING] = consume_switch_timing;
		table[T_SWITCH][T_SIZING] = consume_switch_sizing;
		table[T_SEGMENTS][T_SEGMENT] = consume_segment;
		table[T_SEGMENT][T_TIMING] = consume_segment_timing;
		table[T_BLOCK_TYPES][T_BLOCK_TYPE] = consume_block_type;
		table[T_BLOCK_TYPE][T_PIN_CLASS] = consume_pin_class;
		table[T_PIN_CLASS][T_PIN] = consume_pin;
		table[T_GRID][T_GRID_LOC] = consume_grid_loc;
		table[T_RR_NODES][T_NODE] = consume_node;
		table[T_RR_EDGES][T_EDGE] = consume_edge;
		table[T_NODE][T_LOC] = consume_node_loc;
		table[T_NODE][T_TIMING] = consume_node_timing;
		table[T_NODE][T_SEGMENT] = consume_node_segment;
		table[T_NODE][T_METADATA] = consume_node_metadata;
		table[T_EDGE][T_METADATA] = consume_edge_metadata;
		table[T_METADATA][T_META] = consume_meta;
	}
	/* This works because the first [] is handled by this function,
	 * returning an array of function pointers, which can be then regularly
	 * accessed with the second []. */
	void(**operator[](size_t index))(void) const {
		return table[index];
	}
private:
	void(*table[NUM_TAG_TYPES][NUM_TAG_TYPES])(void);
};
static ParseTableClass parse_table;

/* Attribute lookup is a major source of slowness. We cannot leave it to linear search.
 * However, a std::map of std::strings is too slow for this due to the dynamic allocation.
 *
 * We know that there is an allowed list of attribute names. So, a perfect hash function is again
 * usable. We use it to get lookup table indices from strings while filling in on_start_element.
 * We can then fill a lookup table just like the function lookup. This enables consume_X functions to
 * address the lookup table with, for example, attr_table[T_WIDTH] instead of searching an array
 * of strings with strcmp.
 * If an unknown attribute is found, its value is written to attr_table[T_UNKNOWN].
 *
 * The gperf code is generated just like the one above, with attr_gperf_input.txt. */
enum attr_type: int {
	T_ID, T_NAME, T_TYPE, T_R, T_CIN, T_COUT, T_TDEL, T_MUX_TRANS_SIZE,
	T_BUF_SIZE, T_R_PER_METER, T_C_PER_METER, T_WIDTH, T_HEIGHT, T_PTC, T_X, T_Y,
	T_BLOCK_TYPE_ID, T_WIDTH_OFFSET, T_HEIGHT_OFFSET, T_DIRECTION,
	T_CAPACITY, T_XLOW, T_YLOW, T_XHIGH, T_YHIGH, T_SIDE, T_C, T_SEGMENT_ID,
	T_SRC_NODE, T_SINK_NODE, T_SWITCH_ID, T_CHAN_WIDTH_MAX, T_X_MIN,
	T_Y_MIN, T_X_MAX, T_Y_MAX, T_INFO, T_INDEX, T_TOOL_VERSION, T_TOOL_COMMENT,
	T_UNKNOWN
};
enum { NUM_ATTR_TYPES = 41 };
static const char *attr_table[NUM_ATTR_TYPES];

struct t_attr_lookup {const char *name; enum attr_type value;};
static t_attr_lookup attr_wordlist[] = {
	{""},
	{"y", T_Y},
	{""}, {""},
	{"type", T_TYPE},
	{""}, {""}, {""},
	{"buf_size", T_BUF_SIZE},
	{"Tdel", T_TDEL},
	{"y_max", T_Y_MAX},
	{"x", T_X},
	{"tool_comment", T_TOOL_COMMENT},
	{"ptc", T_PTC},
	{"ylow", T_YLOW},
	{"x_max", T_X_MAX},
	{""}, {""},
	{"capacity", T_CAPACITY},
	{"xlow", T_XLOW},
	{"yhigh", T_YHIGH},
	{"height", T_HEIGHT},
	{"width_offset", T_WIDTH_OFFSET},
	{"block_type_id", T_BLOCK_TYPE_ID},
	{"Cout", T_COUT},
	{"xhigh", T_XHIGH},
	{""}, {""},
	{"height_offset", T_HEIGHT_OFFSET},
	{"chan_width_max", T_CHAN_WIDTH_MAX},
	{"width", T_WIDTH},
	{"R", T_R},
	{""}, {""},
	{"name", T_NAME},
	{"y_min", T_Y_MIN},
	{""}, {""}, {""},
	{"side", T_SIDE},
	{"x_min", T_X_MIN},
	{"C", T_C},
	{"tool_version", T_TOOL_VERSION},
	{"src_node", T_SRC_NODE,},
	{"sink_node", T_SINK_NODE},
	{"index", T_INDEX},
	{"R_per_meter", T_R_PER_METER},
	{"id", T_ID},
	{""},
	{"direction", T_DIRECTION},
	{""},
	{"C_per_meter", T_C_PER_METER},
	{""},
	{"Cin", T_CIN},
	{"switch_id", T_SWITCH_ID},
	{"segment_id", T_SEGMENT_ID,},
	{""}, {""}, {""},
	{"info", T_INFO},
	{""}, {""}, {""}, {""},
	{"mux_trans_size", T_MUX_TRANS_SIZE}
};

static unsigned char attr_asso_values[] = {
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 20, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 15, 65,	5, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 0, 10,
	10, 0, 65, 65, 15, 35, 65, 65, 0, 50,
	30, 20, 0, 65, 20, 35,	0, 65, 65, 10,
	 5, 0, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65, 65, 65, 65, 65,
	65, 65, 65, 65, 65, 65
};

static inline unsigned int attr_hash(const char *str, size_t len){
	return len + attr_asso_values[(unsigned char)str[len - 1]] + attr_asso_values[(unsigned char)str[0]];
}

static inline attr_type lookup_attr_type(const char *str){
	enum {
		TOTAL_KEYWORDS = 40,
		MIN_WORD_LENGTH = 1,
		MAX_WORD_LENGTH = 14,
		MIN_HASH_VALUE = 1,
		MAX_HASH_VALUE = 64
	};
	int len = std::strlen(str);
	unsigned int key = attr_hash(str, len);
	if (key <= MAX_HASH_VALUE){
		auto k = &(attr_wordlist[key]);
		const char *s = k->name;
		if(strcmp (str, s) == 0)
			return k->value;
	}
	/* TODO: Maybe print a warning on unknown attributes? */
	return T_UNKNOWN;
}
/* End of gperf code. */

void mk_attr_table(const char **attrs){
	memset(attr_table, 0, NUM_ATTR_TYPES*sizeof(const char *));
	for(const char **c = attrs; c && *c; c += 2){
		attr_table[lookup_attr_type(*c)] = *(c+1);
	}
}
/* Grab an attribute from the attribute map. Throw if not found. */
static inline const char *get_attr(enum attr_type T){
	const char *q = attr_table[T];
	/* TODO: Add attr_type to attr string lookup table for errors? */
	if(!q) vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Required attribute %d not present.", T);
	return q;
}
/* Grab an attribute from the array of attributes. Return NULL if not found. */
static inline const char *get_attr_optional(enum attr_type T){
	return attr_table[T];
}

/*loads the given RR_graph file into the appropriate data structures
 * as specified by read_rr_graph_name. Set up correct routing data
 * structures as well */
void load_rr_file(const t_graph_type graph_type,
		const DeviceGrid& grid,
		t_chan_width nodes_per_chan,
		const std::vector<t_segment_inf>& segment_inf,
		const enum e_base_cost_type base_cost_type,
		int *wire_to_rr_ipin_switch,
		const char* read_rr_graph_name) {

	vtr::ScopedStartFinishTimer timer("Loading routing resource graph");
	if (vtr::check_file_name_extension(read_rr_graph_name, ".xml") == false) {
		VTR_LOG_WARN(
				"RR graph file '%s' may be in incorrect format. "
				"Expecting .xml format\n",
				read_rr_graph_name);
	}
	auto& device_ctx = g_vpr_ctx.mutable_device();
	chan_width = &nodes_per_chan;
	g_grid = &grid;

	/* First clear the previous rr_graph and reset previous global state
	 *  in case this gets called twice. TODO: what else global vars to clear? */
	delete [] count_for_wire_to_ipin_switches;
	count_for_wire_to_ipin_switches = NULL;
	most_frequent_switch = {-1, 0};
	device_ctx.rr_nodes.clear();
	device_ctx.rr_switch_inf.clear();

	/* Decode the graph_type */
	bool is_global_graph = (GRAPH_GLOBAL == graph_type ? true : false);

	/* Global routing uses a single longwire track */
	int max_chan_width = (is_global_graph ? 1 : nodes_per_chan.max);
	VTR_ASSERT(max_chan_width > 0);

	VTR_LOG("Starting to build routing resource graph...\n");

	/* Start the parser. The SAX parser's handlers will consume the nodes. */
	sax_handler.startElement = on_start_element;
	sax_handler.endElement = on_end_element;
	sax_handler.characters = on_characters;
	std::ifstream F(read_rr_graph_name);
	char buffer[1048576];
	auto ctx = xmlCreatePushParserCtxt(&sax_handler, NULL, NULL, 0, read_rr_graph_name);
	do {
		F.read(buffer, 1048575);
		xmlParseChunk(ctx, buffer, F.gcount(), 0);
	} while(F);
	xmlParseChunk(ctx, buffer, 0, 1);
	xmlFreeParserCtxt(ctx);

	/* Fill in *wire_to_rr_ipin_switch, free the array allocated for tracking it. */
	*wire_to_rr_ipin_switch = most_frequent_switch.id;
	delete [] count_for_wire_to_ipin_switches;

	/* Partition the rr graph edges for efficient access to configurable/non-configurable edge subsets. */
	partition_rr_graph_edges(device_ctx);
	process_rr_node_indices(grid);
	init_fan_in(device_ctx.rr_nodes, device_ctx.rr_nodes.size());

	/* Set the cost index and seg id information. */
	set_cost_indices(is_global_graph, segment_inf.size());
	alloc_and_load_rr_indexed_data(segment_inf, device_ctx.rr_node_indices,
		max_chan_width, *wire_to_rr_ipin_switch, base_cost_type);
	process_seg_id();

	/* hoist chan_width */
	device_ctx.chan_width = nodes_per_chan;

	if (getEchoEnabled() && isEchoFileEnabled(E_ECHO_RR_GRAPH)) {
		dump_rr_graph(getEchoFileName(E_ECHO_RR_GRAPH));
	}
	check_rr_graph(graph_type, grid, device_ctx.block_types);
}
/* Handle a new element's start, like <node capacity=...> */
void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs){
	const char *name = (const char *)_name;
	const char **attrs = (const char **)_attrs;

	tag_type current_tag = lookup_tag(name);
	/* Prepare the attribute lookup table. */
	mk_attr_table(attrs);

	/* Handle the first tag. */
	if(parser_stack_top == -1){
		if(strcmp(name, "rr_graph") == 0){
			parser_stack[0] = T_RR_GRAPH;
			parser_stack_top = 0;
			const char *tool_version = get_attr_optional(T_TOOL_VERSION);
			if(tool_version != NULL && std::strcmp(tool_version, vtr::VERSION) != 0){
				VTR_LOG("\n");
				VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s, compatibility issues may arise.\n", tool_version, vtr::VERSION);
				VTR_LOG("\n");
			}

			std::string correct_string = "Generated from arch file " + std::string(get_arch_file_name());
			const char *tool_comment = get_attr_optional(T_TOOL_COMMENT);
			if(tool_comment != NULL && correct_string != tool_comment){
				VTR_LOG("\n");
				VTR_LOG_WARN("This RR graph file is based on %s while your input architecture file is %s, compatibility issues may arise.\n", tool_comment, get_arch_file_name());
				VTR_LOG("\n");
			}
		} else {
			throw std::runtime_error("No <rr_graph> tag found in RR graph file.");
		}
		return;
	}

	auto prev_tag = parser_stack[parser_stack_top];
	parser_stack_top++;
	parser_stack[parser_stack_top] = current_tag;

	/* Look up callback function from current and previous tags. */
	auto fn = parse_table[prev_tag][current_tag];
	if(fn != NULL){
		(*fn)();
		return;
	}
	/* TODO: Maybe implement reverse enum lookup for this. */
	vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Unexpected node <%d> in <%d>.", current_tag, prev_tag);
	return;
}

void on_end_element(void *ctx, const xmlChar *name){
	parser_stack_top--;
}

/* Complete adding metadata. What we get here is the value of the <meta> node. Only by
 * the time we get it, we know all the required information to make a new meta struct, so it's handled here. */
void on_characters(void *ctx, const xmlChar *_ch, int len){
	if(parser_stack_top == -1) return;
	const char *ch = (const char *)_ch;
	char text[1024];
	auto top = parser_stack[parser_stack_top];
	if(top == T_META){
		strncpy(text, ch, len);
		if(current_meta_place == NODE){
			vpr::add_rr_node_metadata(current_node_id, current_meta_name, text);
		} else if(current_meta_place == EDGE){
			vpr::add_rr_edge_metadata(current_edge.src_id, current_edge.sink_id, current_edge.switch_id,
								current_meta_name, text);
		}
	}
}


void consume_channels(void){
	return;
}
void consume_switches(void){
	return;
}
void consume_segments(void){
	return;
}
void consume_block_types(void){
	return;
}
void consume_grid(void){
	return;
}
void consume_rr_nodes(void){
	return;
}
void consume_rr_edges(void){
	return;
}
/* Load channel info into chan_width(nodes_per_chan in load_rr_file) */
void consume_channel(void){
	chan_width->max = std::atoi(get_attr(T_CHAN_WIDTH_MAX));
	chan_width->x_min = std::atoi(get_attr(T_X_MIN));
	chan_width->y_min = std::atoi(get_attr(T_Y_MIN));
	chan_width->x_max = std::atoi(get_attr(T_X_MAX));
	chan_width->y_max = std::atoi(get_attr(T_Y_MAX));
}
void consume_x_list(void){
	int index = std::atoi(get_attr(T_INDEX));
	chan_width->x_list[index] = std::atof(get_attr(T_INFO));
}
void consume_y_list(void){
	int index = std::atoi(get_attr(T_INDEX));
	chan_width->y_list[index] = std::atof(get_attr(T_INFO));
}

/* Process switch info and push it back to device_ctx.rr_switch_inf[]. When <timing> or <sizing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_switch_inf[] and continues to fill it.
 * TODO: Switch types are in a namespace SwitchType but no other thing-type is. Figure out why. */
void consume_switch(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	t_rr_switch_inf sw = {};
	const char *name = get_attr_optional(T_NAME);
	if(name != NULL) sw.name = vtr::strdup(name);

	std::string type = get_attr(T_TYPE);
	if(type == "mux") sw.set_type(SwitchType::MUX);
	else if(type == "tristate") sw.set_type(SwitchType::TRISTATE);
	else if(type == "pass_gate") sw.set_type(SwitchType::PASS_GATE);
	else if(type == "short") sw.set_type(SwitchType::SHORT);
	else if(type == "buffer") sw.set_type(SwitchType::BUFFER);
	else VPR_THROW(VPR_ERROR_ROUTE, "Invalid switch type %s\n", type.c_str());
	device_ctx.rr_switch_inf.push_back(sw);
}
/* map's operator[] gives default value for nonexistent keys:
 * http://www.cplusplus.com/reference/map/map/operator%5B%5D/ */
void consume_switch_timing(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();

	const char *R = get_attr_optional(T_R);
	if(R != NULL) sw.R = std::atof(R);
	const char *Cin = get_attr_optional(T_CIN);
	if(Cin != NULL) sw.Cin = std::atof(Cin);
	const char *Cout = get_attr_optional(T_COUT);
	if(Cout != NULL) sw.Cout = std::atof(Cout);
	const char *Tdel = get_attr_optional(T_TDEL);
	if(Tdel != NULL) sw.Tdel = std::atof(Tdel);
}
void consume_switch_sizing(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();
	sw.mux_trans_size = std::atof(get_attr(T_MUX_TRANS_SIZE));
	sw.buf_size = std::atof(get_attr(T_BUF_SIZE));
}

/* Segments were initialized from the architecture file. Therefore, we don't need
 * to copy segments into memory but we can check them against the arch file.
 * TODO: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_segment(void){
}
void consume_segment_timing(void){
}

/* Blocks were initialized from the architecture file. Therefore, we don't need
 * to copy block_types into memory but we can check them against the arch file.
 * TODO: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_block_type(void){
	return;
}
void consume_pin_class(void){
	return;
}
void consume_pin(void){
	return;
}

/* Grid was initialized from the architecture file. Therefore, we don't need
 * to copy grid_locs into memory but we can check them against the arch file. */
void consume_grid_loc(void){
	int x = std::atoi(get_attr(T_X));
	int y = std::atoi(get_attr(T_Y));
	const t_grid_tile& grid_tile = (*g_grid)[x][y];

	int block_type_id = std::atoi(get_attr(T_BLOCK_TYPE_ID));
	if (grid_tile.type->index != block_type_id) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's block_type_id at (%d, %d): arch used ID %d, RR graph used ID %d.", x, y,
					 (grid_tile.type->index), block_type_id);
		 }
		 if (grid_tile.width_offset != std::atof(get_attr(T_WIDTH_OFFSET))) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's width_offset at (%d, %d)", x, y);
	}
		 if (grid_tile.width_offset !=  std::atof(get_attr(T_HEIGHT_OFFSET))) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's height_offset at (%d, %d)", x, y);
	}
}

/* Process node info and push it back to device_ctx.rr_nodes[]. When <loc> or <timing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_nodes[] and continues to fill it. */
void consume_node(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	current_node_id = std::atoi(get_attr(T_ID));
	t_rr_node node;
	const char *type = get_attr(T_TYPE);
	if(strcmp(type, "CHANX") == 0){
		node.set_type(CHANX);
	} else if(strcmp(type, "CHANY") == 0){
		node.set_type(CHANY);
	} else if(strcmp(type, "SOURCE") == 0){
		node.set_type(SOURCE);
	} else if(strcmp(type, "SINK") == 0){
		node.set_type(SINK);
	} else if(strcmp(type, "OPIN") == 0){
		node.set_type(OPIN);
	} else if(strcmp(type, "IPIN") == 0){
		node.set_type(IPIN);
	} else {
		vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
			"Valid inputs for class types are \"CHANX\", \"CHANY\",\"SOURCE\", \"SINK\",\"OPIN\", and \"IPIN\".");
	}
	if(node.type() == CHANX || node.type() == CHANY){
		const char *dir = get_attr(T_DIRECTION);
		if(strcmp(dir, "INC_DIR") == 0){
			node.set_direction(INC_DIRECTION);
		} else if(strcmp(dir, "DEC_DIR") == 0){
			node.set_direction(DEC_DIRECTION);
		} else if(strcmp(dir, "BI_DIR") == 0){
			node.set_direction(BI_DIRECTION);
		} else {
			VTR_ASSERT(strcmp(dir, "NO_DIR") == 0);
			node.set_direction(NO_DIRECTION);
		}
	}
	node.set_capacity(std::atoi(get_attr(T_CAPACITY)));
	device_ctx.rr_nodes.push_back(std::move(node));
}
void consume_node_loc(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes[current_node_id];
	short x1, x2, y1, y2;
	x1 = std::atoi(get_attr(T_XLOW));
	y1 = std::atoi(get_attr(T_YLOW));
	x2 = std::atoi(get_attr(T_XHIGH));
	y2 = std::atoi(get_attr(T_YHIGH));
	node.set_coordinates(x1, y1, x2, y2);
	node.set_ptc_num(std::atoi(get_attr(T_PTC)));
	if(node.type() == IPIN || node.type() == OPIN){
		std::string side = get_attr(T_SIDE);
		if(side == "LEFT") node.set_side(LEFT);
		else if(side == "RIGHT") node.set_side(RIGHT);
		else if(side == "TOP") node.set_side(TOP);
		else {
			VTR_ASSERT(side == "BOTTOM");
			node.set_side(BOTTOM);
		}
	}
}
void consume_node_timing(void){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes[current_node_id];
	float R = 0, C = 0;
	const char *R_text = get_attr_optional(T_R);
	if(R_text != NULL) R = std::atof(R_text);
	const char *C_text = get_attr_optional(T_C);
	if(C_text != NULL) C = std::atof(C_text);
	node.set_rc_index(find_create_rr_rc_data(R, C));
}

static std::unordered_map<int, int> seg_id_map;
/* Segments are different: vpr wants to process the previous data before associating
 * segment_ids with nodes. I have no idea why. But we give in and fill a map with
 * segment_ids to know which node ID corresponds to which segment ID. After the
 * whole parsing, segments will be inserted using those IDs. */
void consume_node_segment(void){
	const char *segment_id = get_attr_optional(T_SEGMENT_ID);
	if(segment_id != NULL){
		seg_id_map[current_node_id] = std::atoi(segment_id);
	}
}

/* Since <metadata> involves a child element *and* a text node, this is a bit hard.
 * We set up the current <meta> struct in global state in the start_element handlers(here)
 * and push it in the on_characters handle, where we have the full information. */
void consume_node_metadata(void){
	current_meta_place = NODE;
}
void consume_edge_metadata(void){
	current_meta_place = EDGE;
}
void consume_meta(void){
	current_meta_name = get_attr(T_NAME);
}

/* Add an edge to the source node, save it in global variable current_edge.
 * Also track the most frequently appearing switch that connects a CHANX/CHANY node
 * to a IPIN node. This is done here because there is no easy way to iterate over all edges. */
void consume_edge(void){
	int source_node_id, sink_node_id, switch_id;
	auto& device_ctx = g_vpr_ctx.mutable_device();

	current_edge.src_id = source_node_id = std::atoi(get_attr(T_SRC_NODE));
	current_edge.sink_id = sink_node_id = std::atoi(get_attr(T_SINK_NODE));
	current_edge.switch_id = switch_id = std::atoi(get_attr(T_SWITCH_ID));
	auto& source_node = device_ctx.rr_nodes[source_node_id];
	source_node.add_edge(sink_node_id, switch_id);

	auto& sink_node = device_ctx.rr_nodes[sink_node_id];
	if(count_for_wire_to_ipin_switches == NULL){
		count_for_wire_to_ipin_switches = new int[device_ctx.rr_switch_inf.size()];
		std::memset(count_for_wire_to_ipin_switches, 0, device_ctx.rr_switch_inf.size());
	}
	if((source_node.type() == CHANX || source_node.type() == CHANY) && sink_node.type() == IPIN){
		int count = count_for_wire_to_ipin_switches[switch_id] + 1;
		if(count > most_frequent_switch.count){
			most_frequent_switch.id = switch_id;
			most_frequent_switch.count = count;
		}
		count_for_wire_to_ipin_switches[switch_id] = count;
	}
}

/* Allocate and load the rr_node look up table. SINK and SOURCE, IPIN and OPIN
 * share the same look up table. CHANX and CHANY have individual look ups */
void process_rr_node_indices(const DeviceGrid& grid) {
	auto& device_ctx = g_vpr_ctx.mutable_device();

	/* Alloc the lookup table */
	auto& indices = device_ctx.rr_node_indices;
	indices.resize(NUM_RR_TYPES);
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

	/* Add the correct node into the vector
	 * Note that CHANX and CHANY 's x and y are swapped due to the chan and seg convention.
	 * Push back temporary incorrect nodes for CHANX and CHANY to set the length of the vector */
	for (size_t inode = 0; inode < device_ctx.rr_nodes.size(); inode++) {
		auto& node = device_ctx.rr_nodes[inode];
		if (node.type() == SOURCE || node.type() == SINK) {
			for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
				for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
					if (node.type() == SOURCE) {
						indices[SOURCE][ix][iy][0].push_back(inode);
						indices[SINK][ix][iy][0].push_back(OPEN);
					} else  {
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
					indices[CHANX][iy][ix][0].push_back(inode);
				}
			}
		} else if (node.type() == CHANY) {
			for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
				for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
					indices[CHANY][ix][iy][0].push_back(inode);
				}
			}
		}
	}

	int count;
	/* CHANX and CHANY need to reevaluated with its ptc num as the correct index */
	for (size_t inode = 0; inode < device_ctx.rr_nodes.size(); inode++) {
		auto& node = device_ctx.rr_nodes[inode];
		if (node.type() == CHANX) {
			for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
				for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
					count = node.ptc_num();
					indices[CHANX][iy][ix][0].at(count) = inode;
				}
			}
		} else if (node.type() == CHANY) {
			for (int ix = node.xlow(); ix <= node.xhigh(); ix++) {
				for (int iy = node.ylow(); iy <= node.yhigh(); iy++) {
					count = node.ptc_num();
					indices[CHANY][ix][iy][0].at(count) = inode;
				}
			}
		}
	}

	// Copy the SOURCE/SINK nodes to all offset positions for blocks with width > 1 and/or height > 1
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

void set_cost_indices(bool is_global_graph, const int num_seg_types){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	// set the cost index in order to load the segment information, rr nodes should be set already
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
	/* Go through each rr_node and use the segment ids to set CHANX and CHANY cost index */
	for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
		auto& node = device_ctx.rr_nodes[i];
		int seg_id = seg_id_map[i];
		/*CHANX and CHANY cost index is dependent on the segment id*/
		if (is_global_graph) {
			node.set_cost_index(0);
		} else if (node.type() == CHANX) {
			node.set_cost_index(CHANX_COST_INDEX_START + seg_id);
		} else if (node.type() == CHANY) {
			node.set_cost_index(CHANX_COST_INDEX_START + num_seg_types + seg_id);
		}
	}
}

/* Only CHANX and CHANY components have a segment id. This function
 * reads in the segment id of each node. */
void process_seg_id() {
	auto& device_ctx = g_vpr_ctx.mutable_device();
	for(int i=0; i<device_ctx.rr_nodes.size(); i++){
		auto& node = device_ctx.rr_nodes[i];
		int seg_id = seg_id_map[i];
		if(node.type() == CHANX || node.type() == CHANY){
			device_ctx.rr_indexed_data[node.cost_index()].seg_index = seg_id;
		} else {
			//-1 for non chanx or chany nodes
			device_ctx.rr_indexed_data[node.cost_index()].seg_index = -1;
		}
	}
}

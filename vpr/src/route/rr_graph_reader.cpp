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
const char *get_attr(const char *name, const char **attrs);
const char *get_attr_optional(const char *name, const char **attrs);
void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs);
void on_end_element(void *ctx, const xmlChar *name);
void on_characters(void *ctx, const xmlChar *ch, int len);

void consume_channels(const char ** attrs);
void consume_switches(const char ** attrs);
void consume_segments(const char ** attrs);
void consume_block_types(const char ** attrs);
void consume_grid(const char ** attrs);
void consume_rr_nodes(const char ** attrs);
void consume_rr_edges(const char ** attrs);
void consume_channel(const char ** attrs);
void consume_x_list(const char ** attrs);
void consume_y_list(const char ** attrs);
void consume_switch(const char ** attrs);
void consume_switch_timing(const char ** attrs);
void consume_switch_sizing(const char ** attrs);
void consume_segment(const char ** attrs);
void consume_segment_timing(const char ** attrs);
void consume_block_type(const char ** attrs);
void consume_pin_class(const char ** attrs);
void consume_pin(const char ** attrs);
void consume_grid_loc(const char ** attrs);
void consume_node(const char ** attrs);
void consume_node_loc(const char ** attrs);
void consume_node_timing(const char ** attrs);
void consume_node_segment(const char ** attrs);
void consume_node_metadata(const char ** attrs);
void consume_meta(const char ** attrs);
void consume_edge(const char ** attrs);
void consume_edge_metadata(const char ** attrs);

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
static std::string current_meta_value;
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

/* Map tag names to ints. This helps us build a lookup table instead of a hashmap,
 * and it also enables us to use an array of ints instead of a std::stack of std::strings as the parser stack. */
enum tag_type : int {
	T_RR_GRAPH = 1,
	T_CHANNELS,
	T_SWITCHES,
	T_SEGMENTS,
	T_BLOCK_TYPES,
	T_GRID,
	T_RR_NODES,
	T_RR_EDGES,
	T_CHANNEL,
	T_X_LIST,
	T_Y_LIST,
	T_SWITCH,
	T_TIMING,
	T_SIZING,
	T_SEGMENT,
	T_BLOCK_TYPE,
	T_PIN_CLASS,
	T_PIN,
	T_GRID_LOC,
	T_NODE,
	T_EDGE,
	T_METADATA,
	T_META,
	T_LOC,
};
static std::unordered_map<std::string, tag_type> tag_map = {
	{"rr_graph", T_RR_GRAPH},
	{"channels", T_CHANNELS},
	{"switches", T_SWITCHES},
	{"segments", T_SEGMENTS},
	{"block_types", T_BLOCK_TYPES},
	{"grid", T_GRID},
	{"rr_nodes", T_RR_NODES},
	{"rr_edges", T_RR_EDGES},
	{"channel", T_CHANNEL},
	{"x_list", T_X_LIST},
	{"y_list", T_Y_LIST},
	{"switch", T_SWITCH},
	{"timing", T_TIMING},
	{"sizing", T_SIZING},
	{"segment", T_SEGMENT},
	{"block_type", T_BLOCK_TYPE},
	{"pin_class", T_PIN_CLASS},
	{"pin", T_PIN},
	{"grid_loc", T_GRID_LOC},
	{"node", T_NODE},
	{"edge", T_EDGE},
	{"metadata", T_METADATA},
	{"meta", T_META},
	{"loc", T_LOC},
};

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
	void(**operator[](size_t index))(const char **) const {
		return table[index];
	}
private:
	void(*table[32][32])(const char **);
};
static ParseTableClass parse_table;

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

/* Grab an attribute from the array of attributes. Throw if not found. */
const char *get_attr(const char *name, const char **attrs){
	for(const char **c = attrs; c && *c; c += 2){
		if(strcmp(*c, name) == 0) return *(c+1);
	}
	/* TODO: Give line or tag information here? */
	vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Required attribute %s not present.", name);
}

/* Grab an attribute from the array of attributes. Return NULL if not found. */
const char *get_attr_optional(const char *name, const char **attrs){
	for(const char **c = attrs; c && *c; c += 2){
		if(strcmp(*c, name) == 0) return *(c+1);
	}
	return NULL;
}

/* Handle a new element's start, like <node capacity=...> */
void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs){
	const char *name = (const char *)_name;
	const char **attrs = (const char **)_attrs;

	tag_type current_tag = tag_map[name];
	if(current_tag == 0)
		vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Unrecognized tag <%s>.", name);

	/* Handle the first tag. */
	if(parser_stack_top == -1){
		if(strcmp(name, "rr_graph") == 0){
			parser_stack[0] = T_RR_GRAPH;
			parser_stack_top = 0;
			const char *tool_version = get_attr_optional("tool_version", attrs);
			if(tool_version != NULL && std::strcmp(tool_version, vtr::VERSION) != 0){
				VTR_LOG("\n");
				VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s, compatibility issues may arise.\n", tool_version, vtr::VERSION);
				VTR_LOG("\n");
			}

			std::string correct_string = "Generated from arch file " + std::string(get_arch_file_name());
			const char *tool_comment = get_attr_optional("tool_comment", attrs);
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
		(*fn)(attrs);
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
		current_meta_value = std::string(text);
		if(current_meta_place == NODE){
			vpr::add_rr_node_metadata(current_node_id, current_meta_name, current_meta_value);
		} else if(current_meta_place == EDGE){
			vpr::add_rr_edge_metadata(current_edge.src_id, current_edge.sink_id, current_edge.switch_id,
								current_meta_name, current_meta_value);
		}
	}
}


void consume_channels(const char **attrs){
	return;
}
void consume_switches(const char **attrs){
	return;
}
void consume_segments(const char **attrs){
	return;
}
void consume_block_types(const char **attrs){
	return;
}
void consume_grid(const char **attrs){
	return;
}
void consume_rr_nodes(const char **attrs){
	return;
}
void consume_rr_edges(const char **attrs){
	return;
}
/* Load channel info into chan_width(nodes_per_chan in load_rr_file) */
void consume_channel(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	chan_width->max = std::atoi(get_attr("chan_width_max", attrs));
	chan_width->x_min = std::atoi(get_attr("x_min", attrs));
	chan_width->y_min = std::atoi(get_attr("y_min", attrs));
	chan_width->x_max = std::atoi(get_attr("x_max", attrs));
	chan_width->y_max = std::atoi(get_attr("y_max", attrs));
}
void consume_x_list(const char **attrs){
	int index = std::atoi(get_attr("index", attrs));
	chan_width->x_list[index] = std::atof(get_attr("info", attrs));
}
void consume_y_list(const char **attrs){
	int index = std::atoi(get_attr("index", attrs));
	chan_width->y_list[index] = std::atof(get_attr("info", attrs));
}

/* Process switch info and push it back to device_ctx.rr_switch_inf[]. When <timing> or <sizing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_switch_inf[] and continues to fill it.
 * TODO: Switch types are in a namespace SwitchType but no other thing-type is. Figure out why. */
void consume_switch(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	t_rr_switch_inf sw = {};
	const char *name = get_attr_optional("name", attrs);
	if(name != NULL) sw.name = vtr::strdup(name);

	std::string type = get_attr("type", attrs);
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
void consume_switch_timing(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();

	const char *R = get_attr_optional("R", attrs);
	if(R != NULL) sw.R = std::atof(R);
	const char *Cin = get_attr_optional("Cin", attrs);
	if(Cin != NULL) sw.Cin = std::atof(Cin);
	const char *Cout = get_attr_optional("Cout", attrs);
	if(Cout != NULL) sw.Cout = std::atof(Cout);
	const char *Tdel = get_attr_optional("Tdel", attrs);
	if(Tdel != NULL) sw.Tdel = std::atof(Tdel);
}
void consume_switch_sizing(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();
	sw.mux_trans_size = std::atof(get_attr("mux_trans_size", attrs));
	sw.buf_size = std::atof(get_attr("buf_size", attrs));
}

/* Segments were initialized from the architecture file. Therefore, we don't need
 * to copy segments into memory but we can check them against the arch file.
 * TODO: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_segment(const char **attrs){
}
void consume_segment_timing(const char **attrs){
}

/* Blocks were initialized from the architecture file. Therefore, we don't need
 * to copy block_types into memory but we can check them against the arch file.
 * TODO: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_block_type(const char **attrs){
	return;
}
void consume_pin_class(const char **attrs){
	return;
}
void consume_pin(const char **attrs){
	return;
}

/* Grid was initialized from the architecture file. Therefore, we don't need
 * to copy grid_locs into memory but we can check them against the arch file. */
void consume_grid_loc(const char **attrs){
	int x = std::atoi(get_attr("x", attrs));
	int y = std::atoi(get_attr("y", attrs));
	const t_grid_tile& grid_tile = (*g_grid)[x][y];

	int block_type_id = std::atoi(get_attr("block_type_id", attrs));
	if (grid_tile.type->index != block_type_id) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's block_type_id at (%d, %d): arch used ID %d, RR graph used ID %d.", x, y,
					 (grid_tile.type->index), block_type_id);
		 }
		 if (grid_tile.width_offset != std::atof(get_attr("width_offset", attrs))) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's width_offset at (%d, %d)", x, y);
	}
		 if (grid_tile.width_offset !=  std::atof(get_attr("height_offset", attrs))) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's height_offset at (%d, %d)", x, y);
	}
}

/* Process node info and push it back to device_ctx.rr_nodes[]. When <loc> or <timing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_nodes[] and continues to fill it. */
void consume_node(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	t_rr_node node;
	current_node_id = std::atoi(get_attr("id", attrs));
	std::string type = get_attr("type", attrs);
	if(type == "CHANX"){
		node.set_type(CHANX);
	} else if(type == "CHANY"){
		node.set_type(CHANY);
	} else if(type == "SOURCE"){
		node.set_type(SOURCE);
	} else if(type == "SINK"){
		node.set_type(SINK);
	} else if(type == "OPIN"){
		node.set_type(OPIN);
	} else if(type == "IPIN"){
		node.set_type(IPIN);
	} else {
		vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
			"Valid inputs for class types are \"CHANX\", \"CHANY\",\"SOURCE\", \"SINK\",\"OPIN\", and \"IPIN\".");
	}
	if(node.type() == CHANX || node.type() == CHANY){
		std::string dir = get_attr("direction", attrs);
		if(dir == "INC_DIR"){
			node.set_direction(INC_DIRECTION);
		} else if(dir == "DEC_DIR"){
			node.set_direction(DEC_DIRECTION);
		} else if(dir == "BI_DIR"){
			node.set_direction(BI_DIRECTION);
		} else {
			VTR_ASSERT(dir == "NO_DIR");
			node.set_direction(NO_DIRECTION);
		}
	}
	node.set_capacity(std::atoi(get_attr("capacity", attrs)));
	node.set_num_edges(0);
	device_ctx.rr_nodes.push_back(std::move(node));
}
void consume_node_loc(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes[current_node_id];
	short x1, x2, y1, y2;
	x1 = std::atoi(get_attr("xlow", attrs));
	y1 = std::atoi(get_attr("ylow", attrs));
	x2 = std::atoi(get_attr("xhigh", attrs));
	y2 = std::atoi(get_attr("yhigh", attrs));
	node.set_coordinates(x1, y1, x2, y2);
	node.set_ptc_num(std::atoi(get_attr("ptc", attrs)));
	if(node.type() == IPIN || node.type() == OPIN){
		std::string side = get_attr("side", attrs);
		if(side == "LEFT") node.set_side(LEFT);
		else if(side == "RIGHT") node.set_side(RIGHT);
		else if(side == "TOP") node.set_side(TOP);
		else {
			VTR_ASSERT(side == "BOTTOM");
			node.set_side(BOTTOM);
		}
	}
}
void consume_node_timing(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes[current_node_id];
	float R = 0, C = 0;
	const char *R_text = get_attr_optional("R", attrs);
	if(R_text != NULL) R = std::atof(R_text);
	const char *C_text = get_attr_optional("C", attrs);
	if(C_text != NULL) C = std::atof(C_text);
	node.set_rc_index(find_create_rr_rc_data(R, C));
}

static std::unordered_map<int, int> seg_id_map;
/* Segments are different: vpr wants to process the previous data before associating
 * segment_ids with nodes. I have no idea why. But we give in and fill a map with
 * segment_ids to know which node ID corresponds to which segment ID. After the
 * whole parsing, segments will be inserted using those IDs. */
void consume_node_segment(const char **attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	const char *segment_id = get_attr_optional("segment_id", attrs);
	if(segment_id != NULL){
		seg_id_map[current_node_id] = std::atoi(segment_id);
	}
}

/* Since <metadata> involves a child element *and* a text node, this is a bit hard.
 * We set up the current <meta> struct in global state in the start_element handlers(here)
 * and push it in the on_characters handle, where we have the full information. */
void consume_node_metadata(const char **attrs){
	current_meta_place = NODE;
}
void consume_edge_metadata(const char **attrs){
	current_meta_place = EDGE;
}
void consume_meta(const char **attrs){
	current_meta_name = get_attr("name", attrs);
}

/* Add an edge to the source node, save it in global variable current_edge.
 * Also track the most frequently appearing switch that connects a CHANX/CHANY node
 * to a IPIN node. This is done here because there is no easy way to iterate over all edges. */
void consume_edge(const char ** attrs){
	int source_node_id, sink_node_id, switch_id;
	auto& device_ctx = g_vpr_ctx.mutable_device();

	current_edge.src_id = source_node_id = std::atoi(get_attr("src_node", attrs));
	current_edge.sink_id = sink_node_id = std::atoi(get_attr("sink_node", attrs));
	current_edge.switch_id = switch_id = std::atoi(get_attr("switch_id", attrs));
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

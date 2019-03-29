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

typedef std::unordered_map<std::string, std::string> AttributeMap;

/********************* Subroutines local to this module *******************/
void load_rr_file(const char *name);
void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs);
void on_end_element(void *ctx, const xmlChar *name);
void on_characters(void *ctx, const xmlChar *ch, int len);

void consume_channels(AttributeMap& attrs);
void consume_switches(AttributeMap& attrs);
void consume_segments(AttributeMap& attrs);
void consume_block_types(AttributeMap& attrs);
void consume_grid(AttributeMap& attrs);
void consume_rr_nodes(AttributeMap& attrs);
void consume_rr_edges(AttributeMap& attrs);
void consume_channel(AttributeMap& attrs);
void consume_x_list(AttributeMap& attrs);
void consume_y_list(AttributeMap& attrs);
void consume_switch(AttributeMap& attrs);
void consume_switch_timing(AttributeMap& attrs);
void consume_switch_sizing(AttributeMap& attrs);
void consume_segment(AttributeMap& attrs);
void consume_segment_timing(AttributeMap& attrs);
void consume_block_type(AttributeMap& attrs);
void consume_pin_class(AttributeMap& attrs);
void consume_pin(AttributeMap& attrs);
void consume_grid_loc(AttributeMap& attrs);
void consume_node(AttributeMap& attrs);
void consume_node_loc(AttributeMap& attrs);
void consume_node_timing(AttributeMap& attrs);
void consume_node_segment(AttributeMap& attrs);
void consume_node_metadata(AttributeMap& attrs);
void consume_meta(AttributeMap& attrs);
void consume_edge(AttributeMap& attrs);
void consume_edge_metadata(AttributeMap& attrs);

void process_edges(int *wire_to_rr_ipin_switch, int num_rr_switches);
void process_rr_node_indices(const DeviceGrid& grid);
void set_cost_indices(bool is_global_graph, const int num_seg_types);
void process_seg_id();

/********************* Global variables for this module *******************/
static std::stack <const char *> parser_stack;
static xmlSAXHandler sax_handler = {};

/* We need to build the current <meta> node piece by piece here. */
static t_offset current_meta_o = {};
static std::string current_meta_name;
static std::string current_meta_value;
static enum {NODE, EDGE} current_meta_place;

/* Edges create trouble when processed sequentially, so we read all into memory.
 * Note that we are not caching edge metadata, they can be read right into device_ctx. */
struct cached_edge { int src_node_id; int sink_node_id; int switch_id; };
static std::vector<cached_edge> cached_edges;

/* hoist pointers to arguments to load_rr_file: we need to access them from SAX handlers */
static t_chan_width *chan_width;
static const DeviceGrid *g_grid;

/*
enum {
	T_RR_GRAPH = 0,
	T_CHANNELS = 1,
	T_SWITCHES = 2,
	T_SEGMENTS = 3,
	T_BLOCK_TYPES = 4,
	T_GRID = 5,
	T_RR_NODES = 6,
	T_RR_EDGES = 7,
	T_CHANNEL = 8,
	T_X_LIST = 9,
	T_Y_LIST = 10,
	T_SWITCH = 11,
	T_TIMING = 12,
	T_SIZING = 13,
	T_SEGMENT = 14,
	T_BLOCK_TYPE = 15,
	T_PIN_CLASS = 16,
	T_PIN = 17,
	T_GRID_LOC = 18,
	T_NODE = 19,
	T_EDGE = 20,
	T_METADATA = 21,
	T_META = 22
} tag_type;
static std::unordered_map<std::string, tag_type> tag_map = {
	T_RR_GRAPH = 0,
	T_CHANNELS = 1,
	T_SWITCHES = 2,
	T_SEGMENTS = 3,
	T_BLOCK_TYPES = 4,
	T_GRID = 5,
	T_RR_NODES = 6,
	T_RR_EDGES = 7,
	T_CHANNEL = 8,
	T_X_LIST = 9,
	T_Y_LIST = 10,
	T_SWITCH = 11,
	T_TIMING = 12,
	T_SIZING = 13,
	T_SEGMENT = 14,
	T_BLOCK_TYPE = 15,
	T_PIN_CLASS = 16,
	T_PIN = 17,
	T_GRID_LOC = 18,
	T_NODE = 19,
	T_EDGE = 20,
	T_METADATA = 21,
	T_META = 22
}
*/

/* A mapping from the previous tag and current tag to the function to call. */
static std::unordered_map<std::string, std::unordered_map<std::string, void(*)(AttributeMap&)>> parse_table = {
		{"rr_graph", {
			{"channels", consume_channels},
			{"switches", consume_switches},
			{"segments", consume_segments},
			{"block_types", consume_block_types},
			{"grid", consume_grid},
			{"rr_nodes", consume_rr_nodes},
			{"rr_edges", consume_rr_edges}
		}},
		{"channels", {
			{"channel", consume_channel},
			{"x_list", consume_x_list},
			{"y_list", consume_y_list},
		}},
		{"switches", {
			{"switch", consume_switch},
		}},
		{"switch", {
			{"timing", consume_switch_timing},
			{"sizing", consume_switch_sizing},
		}},
		{"segments", {
			{"segment", consume_segment},
		}},
		{"segment", {
			{"timing", consume_segment_timing},
		}},
		{"block_types", {
			{"block_type", consume_block_type},
		}},
		{"block_type", {
			{"pin_class", consume_pin_class},
		}},
		{"pin_class", {
			{"pin", consume_pin},
		}},
		{"grid", {
			{"grid_loc", consume_grid_loc},
		}},
		{"rr_nodes", {
			{"node", consume_node},
		}},
		{"rr_edges", {
			{"edge", consume_edge},
		}},
		{"node", {
			{"loc", consume_node_loc},
			{"timing", consume_node_timing},
			{"segment", consume_node_segment},
			{"metadata", consume_node_metadata},
		}},
		{"edge", {
			{"metadata", consume_edge_metadata},
		}},
		{"metadata", {
			{"meta", consume_meta},
		}},
};

/*loads the given RR_graph file into the appropriate data structures
 * as specified by read_rr_graph_name. Set up correct routing data
 * structures as well */
void load_rr_file(const t_graph_type graph_type,
		const DeviceGrid& grid,
		t_chan_width nodes_per_chan,
		const std::vector<t_segment_inf>& segment_inf,
		const DeviceGrid& grid,
		t_chan_width nodes_per_chan,
		const int num_seg_types,
		const t_segment_inf * segment_inf,
		const enum e_base_cost_type base_cost_type,
		int *wire_to_rr_ipin_switch,
		int *num_rr_switches,
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

	/* First clear the previous rr_graph in case this gets called twice. XXX: what else global vars to clear? */
	cached_edges.clear();
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

	/* Process the cached edges. */
	*num_rr_switches = device_ctx.rr_switch_inf.size();
	process_edges(wire_to_rr_ipin_switch, *num_rr_switches);

	/* Partition the rr graph edges for efficient access to configurable/non-configurable edge subsets. */
	partition_rr_graph_edges(device_ctx);
	process_rr_node_indices(grid);
	init_fan_in(device_ctx.rr_nodes, device_ctx.rr_nodes.size());

	/* Set the cost index and seg id information. */
	set_cost_indices(is_global_graph, num_seg_types);
	alloc_and_load_rr_indexed_data(segment_inf, num_seg_types, device_ctx.rr_node_indices,
		max_chan_width, *wire_to_rr_ipin_switch, base_cost_type);
	process_seg_id();

	/* hoist chan_width */
	device_ctx.chan_width = nodes_per_chan;

	if (getEchoEnabled() && isEchoFileEnabled(E_ECHO_RR_GRAPH)) {
		dump_rr_graph(getEchoFileName(E_ECHO_RR_GRAPH));
	}
	check_rr_graph(graph_type, grid, *num_rr_switches, device_ctx.block_types);
}

/* Handle a new element's start like <node capacity=...> */
void on_start_element(void *ctx, const xmlChar *_name, const xmlChar **_attrs){
	const char *name = (const char *)_name;
	const char **attrs = (const char **)_attrs;
	/* Convert attributes to hashtable first. */
	AttributeMap attr_map;
	for(const char **c = attrs; c && *c; c += 2){
		attr_map[*c] = *(c+1);
	}

	if(parser_stack.empty()){
		if(strcmp(name, "rr_graph") == 0){
			parser_stack.push("rr_graph");
			if(attr_map["tool_version"] != "" && attr_map["tool_version"] != vtr::VERSION){
				VTR_LOG("\n");
				VTR_LOG_WARN("This architecture version is for VPR %s while your current VPR version is %s, compatibility issues may arise.\n", attr_map["tool_version"].c_str(), vtr::VERSION);
				VTR_LOG("\n");
			}
			std::string correct_string = "Generated from arch file " + std::string(get_arch_file_name());
			if(attr_map["tool_comment"] != "" && attr_map["tool_comment"] != correct_string){
				VTR_LOG("\n");
				VTR_LOG_WARN("This RR graph file is based on %s while your input architecture file is %s, compatibility issues may arise.\n", attr_map["tool_comment"].c_str(), get_arch_file_name());
				VTR_LOG("\n");
			}
		} else {
			throw std::runtime_error("No <rr_graph> tag found in RR graph file.");
		}
		return;
	}

	auto top = parser_stack.top();
	parser_stack.push(name);

	/* Look up callback function from current and previous tags. */
	auto fn = parse_table[top][name];
	if(fn != NULL){
		(*fn)(attr_map);
		return;
	}
	vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__, "Unexpected node <%s> in <%s>.", name, top);
	return;
}

void on_end_element(void *ctx, const xmlChar *name){
	parser_stack.pop();
}

/* Complete adding metadata. What we get here is the value of the <meta> node. Only by
 * the time we get it, we know all the required information to make a new meta struct, so it's handled here. */
void on_characters(void *ctx, const xmlChar *_ch, int len){
	if(parser_stack.empty()) return;
	const char *ch = (const char *)_ch;
	char text[1024];
	auto top = parser_stack.top();
	if(strcmp(top, "meta") == 0){
		auto& device_ctx = g_vpr_ctx.mutable_device();
		strncpy(text, ch, len);
		current_meta_value = std::string(text);
		if(current_meta_place == NODE){
			auto& node = device_ctx.rr_nodes.back();
			node.add_metadata(current_meta_o, current_meta_name, current_meta_value);
		} else if(current_meta_place == EDGE){
			auto &edge = cached_edges.back();
			auto &node = device_ctx.rr_nodes[edge.src_node_id];
			node.add_edge_metadata(edge.sink_node_id, edge.switch_id,
								current_meta_o, current_meta_name, current_meta_value);
		}
	}
}

void consume_channels(AttributeMap& attrs){
	return;
}
void consume_switches(AttributeMap& attrs){
	return;
}
void consume_segments(AttributeMap& attrs){
	return;
}
void consume_block_types(AttributeMap& attrs){
	return;
}
void consume_grid(AttributeMap& attrs){
	return;
}
void consume_rr_nodes(AttributeMap& attrs){
	return;
}
void consume_rr_edges(AttributeMap& attrs){
	return;
}
/* Load channel info into chan_width(nodes_per_chan in load_rr_file) */
void consume_channel(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	chan_width->max = std::stoi(attrs["chan_width_max"]);
	chan_width->x_min = std::stoi(attrs["x_min"]);
	chan_width->y_min = std::stoi(attrs["y_min"]);
	chan_width->x_max = std::stoi(attrs["x_max"]);
	chan_width->y_max = std::stoi(attrs["y_max"]);
}
void consume_x_list(AttributeMap& attrs){
	int index = std::stoi(attrs["index"]);
	chan_width->x_list[index] = std::stof(attrs["info"]);
}
void consume_y_list(AttributeMap& attrs){
	int index = std::stoi(attrs["index"]);
	chan_width->y_list[index] = std::stof(attrs["info"]);
}

/* Process switch info and push it back to device_ctx.rr_switch_inf[]. When <timing> or <sizing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_switch_inf[] and continues to fill it.
 * TODO: Switch types are in a namespace SwitchType but no other thing-type is. Figure out why. */
void consume_switch(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	t_rr_switch_inf sw = {};
	if(attrs["name"] != "") sw.name = vtr::strdup(attrs["name"].c_str());
	std::string type = attrs["type"];
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
void consume_switch_timing(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();
	if(attrs["R"] != "") sw.R = std::stof(attrs["R"]);
	if(attrs["Cin"] != "") sw.Cin = std::stof(attrs["Cin"]);
	if(attrs["Cout"] != "") sw.Cout = std::stof(attrs["Cout"]);
	if(attrs["Tdel"] != "") sw.Tdel = std::stof(attrs["Tdel"]);
}
void consume_switch_sizing(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& sw = device_ctx.rr_switch_inf.back();
	sw.mux_trans_size = std::stof(attrs["mux_trans_size"]);
	sw.buf_size = std::stof(attrs["buf_size"]);
}

/* Segments were initialized from the architecture file. Therefore, we don't need
 * to copy segments into memory but we can check them against the arch file.
 * TODO: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_segment(AttributeMap& attrs){
}
void consume_segment_timing(AttributeMap& attrs){
}

/* Blocks were initialized from the architecture file. Therefore, we don't need
 * to copy block_types into memory but we can check them against the arch file.
 * XXX: really do this. This requires some global state and it's not the whole point of the SAX
 * implementation, so skipped for now. */
void consume_block_type(AttributeMap& attrs){
	return;
}
void consume_pin_class(AttributeMap& attrs){
	return;
}
void consume_pin(AttributeMap& attrs){
	return;
}
>>>>>>> 925e908e5... initiate rr_graph reader with SAX

/* Grid was initialized from the architecture file. Therefore, we don't need
 * to copy grid_locs into memory but we can check them against the arch file. */
void consume_grid_loc(AttributeMap& attrs){
	int x = std::stoi(attrs["x"]);
	int y = std::stoi(attrs["y"]);
	const t_grid_tile& grid_tile = (*g_grid)[x][y];

	int block_type_id = std::stoi(attrs["block_type_id"]);
	if (grid_tile.type->index != block_type_id) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's block_type_id at (%d, %d): arch used ID %d, RR graph used ID %d.", x, y,
					 (grid_tile.type->index), block_type_id);
		 }
		 if (grid_tile.width_offset != std::stof(attrs["width_offset"])) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's width_offset at (%d, %d)", x, y);
	}
		 if (grid_tile.width_offset != std::stof(attrs["height_offset"])) {
			vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
					"Architecture file does not match RR graph's height_offset at (%d, %d)", x, y);
	}
}

/* Process node info and push it back to device_ctx.rr_nodes[]. When <loc> or <timing> arrives,
 * the corresponding callback picks up the last item in device_ctx.rr_nodes[] and continues to fill it.
 * current_node_id is kept because we need to build a map from node IDs to segment IDs and t_rr_node
 * does not hold IDs.
 * !! Also note that it's assumed that nodes appear in ID order and no ID gaps occur. */
static int current_node_id;
void consume_node(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	t_rr_node node;
	current_node_id = std::stoi(attrs["id"]);
	std::string type = attrs["type"];
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
		std::string dir = attrs["direction"];
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
	node.set_capacity(std::stoi(attrs["capacity"]));
	node.set_num_edges(0);
	device_ctx.rr_nodes.push_back(std::move(node));
}
void consume_node_loc(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes.back();
	short x1, x2, y1, y2;
	x1 = std::stoi(attrs["xlow"]);
	y1 = std::stoi(attrs["ylow"]);
	x2 = std::stoi(attrs["xhigh"]);
	y2 = std::stoi(attrs["yhigh"]);
	node.set_coordinates(x1, y1, x2, y2);
	node.set_ptc_num(std::stoi(attrs["ptc"]));
	if(node.type() == IPIN || node.type() == OPIN){
		std::string side = attrs["side"];
		if(side == "LEFT") node.set_side(LEFT);
		else if(side == "RIGHT") node.set_side(RIGHT);
		else if(side == "TOP") node.set_side(TOP);
		else {
			VTR_ASSERT(side == "BOTTOM");
			node.set_side(BOTTOM);
		}
	}
}
void consume_node_timing(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	auto& node = device_ctx.rr_nodes.back();
	float R = 0, C = 0;
	if(attrs["R"] != "") R = std::stof(attrs["R"]);
	if(attrs["C"] != "") C = std::stof(attrs["C"]);
	node.set_rc_index(find_create_rr_rc_data(R, C));
}

static std::unordered_map<int, int> seg_id_map;
/* Segments are different: vpr wants to process the previous data before associating
 * segment_ids with nodes. I have no idea why. But we give in and fill a map with
 * segment_ids to know which node ID corresponds to which segment ID. After the
 * whole parsing, segments will be inserted using those IDs. */
void consume_node_segment(AttributeMap& attrs){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	if(attrs["segment_id"] != ""){
		seg_id_map[current_node_id] = std::stoi(attrs["segment_id"]);
	}
}

/* Since <metadata> involves a child element *and* a text node, this is a bit hard.
 * We set up the current <meta> struct in global state in the start_element handlers(here)
 * and push it in the on_characters handle, where we have the full information. */
void consume_node_metadata(AttributeMap& attrs){
	current_meta_place = NODE;
}
void consume_edge_metadata(AttributeMap& attrs){
	current_meta_place = EDGE;
}
void consume_meta(AttributeMap& attrs){
	current_meta_o = {0, 0, 0};
	current_meta_name = attrs["name"];
	if(attrs["x_offset"] != "") current_meta_o.x = std::stoi(attrs["x_offset"]);
	if(attrs["y_offset"] != "") current_meta_o.y = std::stoi(attrs["y_offset"]);
	if(attrs["z_offset"] != "") current_meta_o.z = std::stoi(attrs["z_offset"]);
}

/* Cache the edge for further processing. Note that we do not cache the metadata. */
void consume_edge(AttributeMap& attrs){
	cached_edge edge;
	edge.src_node_id = std::stoi(attrs["src_node"]);
	edge.sink_node_id = std::stoi(attrs["sink_node"]);
	edge.switch_id = std::stoi(attrs["switch_id"]);
	cached_edges.push_back(std::move(edge));
}

/* Process the cached edges. */
void process_edges(int *wire_to_rr_ipin_switch, int num_rr_switches){
	auto& device_ctx = g_vpr_ctx.mutable_device();
	std::vector<int> num_edges_for_node;
	num_edges_for_node.resize(device_ctx.rr_nodes.size(), 0);
	std::fill(num_edges_for_node.begin(), num_edges_for_node.end(), 0);
	/* first count edges for all nodes and allocate space for edges in them.
	 * in nodes, edge space is implemented with unique_ptr and it's a pain to "push" into such arrays. */
	for(auto e : cached_edges){
		int src_id = e.src_node_id;
		num_edges_for_node[src_id]++;
		device_ctx.rr_nodes[src_id].set_num_edges(num_edges_for_node[src_id]); /* TODO: is it sensible to do this? */
	}
	/* now reset all counts and place each edge into its own index, incrementing the
	 * count as we go. this is again an artifact from the unique_ptr. */
	fill(num_edges_for_node.begin(), num_edges_for_node.end(), 0);
	for(auto e : cached_edges){
		int src_id = e.src_node_id;
		device_ctx.rr_nodes[src_id].set_edge_sink_node(num_edges_for_node[src_id], e.sink_node_id);
		device_ctx.rr_nodes[src_id].set_edge_switch(num_edges_for_node[src_id], e.switch_id);
		num_edges_for_node[src_id]++;
	}
	/* finally get and store the most frequent switch that connects a CHANX/CHANY node to an IPIN node. */
	std::vector<int> count_for_wire_to_ipin_switches;
	count_for_wire_to_ipin_switches.resize(num_rr_switches, 0);
	struct {int id; int count;} most_frequent_switch = {-1, 0};
	for(auto e: cached_edges){
		auto& source_node = device_ctx.rr_nodes[e.src_node_id];
		auto& sink_node = device_ctx.rr_nodes[e.sink_node_id];
		if((source_node.type() == CHANX || source_node.type() == CHANY) && sink_node.type() == IPIN){
			int count = count_for_wire_to_ipin_switches[e.switch_id] + 1;
			if(count > most_frequent_switch.count){
				most_frequent_switch.id = e.switch_id;
				most_frequent_switch.count = count;
			}
			count_for_wire_to_ipin_switches[e.switch_id] = count;
		}
	}
	*wire_to_rr_ipin_switch = most_frequent_switch.id;
}

/*Allocate and load the rr_node look up table. SINK and SOURCE, IPIN and OPIN
 *share the same look up table. CHANX and CHANY have individual look ups */
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

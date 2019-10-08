/*
 * This file defines the writing rr graph function in XML format.
 * The rr graph is separated into channels, nodes, switches,
 * grids, edges, block types, and segments. Each tag has several
 * children tags such as timing, location, or some general
 * details. Each tag has attributes to describe them */

#include <cstdio>
#include <fstream>
#include <iostream>
#include <string.h>
#include <iomanip>
#include <limits>
#include "vpr_error.h"
#include "globals.h"
#include "read_xml_arch_file.h"
#include "vtr_version.h"
#include "rr_graph_writer.h"
#include "rr_graph.h"

#include "rr_graph_uxsdcxx.h"
#include "serdes_utils.h"
#include "capnp/serialize.h"
#include "rr_graph_uxsdcxx.capnp.h"

/************************ Subroutine definitions ****************************/
void write_rr_graph_xml(const char* file_name, const std::vector<t_segment_inf>& segment_inf);
void write_rr_nodes_xml(uxsd::rr_graph& rr_graph);
void write_rr_edges_xml(uxsd::rr_graph& rr_graph);
void write_rr_graph_capnp(const char* file_name, const std::vector<t_segment_inf>& segment_inf);
void write_rr_nodes_capnp(ucap::RrGraph::Builder& rr_graph);
void write_rr_edges_capnp(ucap::RrGraph::Builder& rr_graph);

/**
 * Write the current rr_graph into file_name.
 * If the file name has the .rr_graph extension, write out a Cap'n Proto message,
 * otherwise write in XML format.
 */
void write_rr_graph(const char* file_name, const std::vector<t_segment_inf>& segment_inf) {
    if (vtr::check_file_name_extension(file_name, ".rr_graph")) {
        write_rr_graph_capnp(file_name, segment_inf);
    } else {
        write_rr_graph_xml(file_name, segment_inf);
    }
    std::cout << "Finished generating RR graph file named " << file_name << std::endl
         << std::endl;
}

/**
 * Write the current rr_graph into file_name in XML format.
 * Copies the rr_graph into uxsdcxx-generated structures and calls uxsd::rr_graph.write() to generate XML.
 */
void write_rr_graph_xml(const char* file_name, const std::vector<t_segment_inf>& segment_inf) {
    auto& device_ctx = g_vpr_ctx.device();
    std::fstream fp;
    std::stringstream header;
    std::string filename_str(file_name);

    uxsd::rr_graph rr_graph = uxsd::rr_graph();

    fp.open(file_name, std::fstream::out | std::fstream::trunc);
    /* Prints out general info for easy error checking*/
    if (!fp.is_open() || !fp.good()) {
        vpr_throw(VPR_ERROR_OTHER, __FILE__, __LINE__,
                  "couldn't open file \"%s\" for generating RR graph file\n", file_name);
    }

    /* We copy over the VPR structures over to the uxsd::rr_graph structures
     * and then call rr_graph.write(fp) to write out to a file. */
    rr_graph.tool_name = "vpr";
    rr_graph.tool_version = vtr::VERSION;
    std::string tool_comment = std::string("Generated from arch file ") + get_arch_file_name();
    rr_graph.tool_comment = tool_comment.c_str();

    /* Copy channels. */
    auto& channel = rr_graph.channels.channel;
    channel.chan_width_max = device_ctx.chan_width.max;
    channel.x_min = device_ctx.chan_width.x_min;
    channel.y_min = device_ctx.chan_width.y_min;
    channel.x_max = device_ctx.chan_width.x_max;
    channel.y_max = device_ctx.chan_width.y_max;
    for (size_t i = 0; i < device_ctx.grid.height() - 1; i++) {
        uxsd::t_x_list x;
        x.index = i;
        x.info = device_ctx.chan_width.x_list[i];
        rr_graph.channels.x_lists.push_back(x);
    }
    for (size_t i = 0; i < device_ctx.grid.width() - 1; i++) {
        uxsd::t_y_list y;
        y.index = i;
        y.info = device_ctx.chan_width.y_list[i];
        rr_graph.channels.y_lists.push_back(y);
    }

    /* Copy switches. */
    for (size_t i = 0; i < device_ctx.rr_switch_inf.size(); i++) {
        auto& rr_switch = device_ctx.rr_switch_inf[i];
        uxsd::t_switch sw;
        sw.id = i;
        sw.name = rr_switch.name;
        uxsd::enum_switch_type sw_type_map[] = {
            uxsd::enum_switch_type::MUX,
            uxsd::enum_switch_type::TRISTATE,
            uxsd::enum_switch_type::PASS_GATE,
            uxsd::enum_switch_type::SHORT,
            uxsd::enum_switch_type::BUFFER,
        };
        sw.type = sw_type_map[(int)rr_switch.type()];
        sw.has_timing = true;
        sw.timing.R = rr_switch.R;
        sw.timing.Cin = rr_switch.Cin;
        sw.timing.Cout = rr_switch.Cout;
        sw.timing.Cinternal = rr_switch.Cinternal;
        sw.timing.Tdel = rr_switch.Tdel;
        sw.sizing.mux_trans_size = rr_switch.mux_trans_size;
        sw.sizing.buf_size = rr_switch.buf_size;
        rr_graph.switches.switches.push_back(sw);
    }

    /* Copy segments. */
    for (size_t i = 0; i < segment_inf.size(); i++) {
        auto& rr_segment = segment_inf[i];
        uxsd::t_segment seg;
        seg.id = i;
        seg.name = rr_segment.name.c_str();
        seg.has_timing = true;
        seg.timing.R_per_meter = rr_segment.Rmetal;
        seg.timing.C_per_meter = rr_segment.Cmetal;
        rr_graph.segments.segments.push_back(seg);
    }

    /* Copy block types. */
    for (auto& rr_bt : device_ctx.physical_tile_types) {
        uxsd::t_block_type bt;
        bt.id = rr_bt.index;
        bt.name = rr_bt.name;
        bt.width = rr_bt.width;
        bt.height = rr_bt.height;
        for (int j = 0; j < rr_bt.num_class; j++) {
            auto& rr_class = rr_bt.class_inf[j];
            uxsd::t_pin_class pc;
            if (rr_class.type == -1)
                pc.type = uxsd::enum_pin_type::OPEN;
            else if (rr_class.type == 0)
                pc.type = uxsd::enum_pin_type::OUTPUT;
            else if (rr_class.type == 1)
                pc.type = uxsd::enum_pin_type::INPUT;
            else
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid pin class type %d.\n", rr_class.type);
            for (int k = 0; k < rr_class.num_pins; k++) {
                auto& rr_pin = rr_class.pinlist[k];
                uxsd::t_pin pin;
                pin.ptc = rr_pin;
                pin.value = uxsd::char_pool.add(block_type_pin_index_to_name(&rr_bt, rr_pin).c_str());
                pc.pins.push_back(pin);
            }
            bt.pin_classes.push_back(pc);
        }
        rr_graph.block_types.block_types.push_back(bt);
    }

    /* Copy over grid to the uxsd structures. */
    for (size_t x = 0; x < device_ctx.grid.width(); x++) {
        for (size_t y = 0; y < device_ctx.grid.height(); y++) {
            auto& rr_grid_tile = device_ctx.grid[x][y];
            uxsd::t_grid_loc loc;
            loc.x = x;
            loc.y = y;
            loc.block_type_id = rr_grid_tile.type->index;
            loc.width_offset = rr_grid_tile.width_offset;
            loc.height_offset = rr_grid_tile.height_offset;
            rr_graph.grid.grid_locs.push_back(loc);
        }
    }

    write_rr_nodes_xml(rr_graph);
    write_rr_edges_xml(rr_graph);

    std::cout << "Writing RR graph" << std::endl;
    fp.precision(std::numeric_limits<float>::max_digits10);
    rr_graph.write(fp);
    fp.close();

    /* Free up uxsdcxx memory. */
    uxsd::clear_pools();
    uxsd::clear_strings();
}

/* write_rr_graph_xml helper. */
void write_rr_nodes_xml(uxsd::rr_graph& rr_graph) {
    auto& device_ctx = g_vpr_ctx.device();
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        auto& rr_node = device_ctx.rr_nodes[i];
        uxsd::t_node node = {};
        node.id = i;
        if (rr_node.type() == CHANX)
            node.type = uxsd::enum_node_type::CHANX;
        else if (rr_node.type() == CHANY)
            node.type = uxsd::enum_node_type::CHANY;
        else if (rr_node.type() == SOURCE)
            node.type = uxsd::enum_node_type::SOURCE;
        else if (rr_node.type() == SINK)
            node.type = uxsd::enum_node_type::SINK;
        else if (rr_node.type() == OPIN)
            node.type = uxsd::enum_node_type::OPIN;
        else if (rr_node.type() == IPIN)
            node.type = uxsd::enum_node_type::IPIN;
        else
            VPR_THROW(VPR_ERROR_ROUTE, "Invalid node type %d.\n", rr_node.type());
        if (rr_node.type() == CHANX || rr_node.type() == CHANY) {
            if (rr_node.direction() == INC_DIRECTION)
                node.direction = uxsd::enum_node_direction::INC_DIR;
            else if (rr_node.direction() == DEC_DIRECTION)
                node.direction = uxsd::enum_node_direction::DEC_DIR;
            else if (rr_node.direction() == BI_DIRECTION)
                node.direction = uxsd::enum_node_direction::BI_DIR;
            else
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid node direction %d.\n", rr_node.direction());
        }
        node.capacity = rr_node.capacity();
        node.loc.xlow = rr_node.xlow();
        node.loc.ylow = rr_node.ylow();
        node.loc.xhigh = rr_node.xhigh();
        node.loc.yhigh = rr_node.yhigh();
        if (rr_node.type() == IPIN || rr_node.type() == OPIN) {
            if (rr_node.side() == LEFT)
                node.loc.side = uxsd::enum_loc_side::LEFT;
            else if (rr_node.side() == RIGHT)
                node.loc.side = uxsd::enum_loc_side::RIGHT;
            else if (rr_node.side() == TOP)
                node.loc.side = uxsd::enum_loc_side::TOP;
            else if (rr_node.side() == BOTTOM)
                node.loc.side = uxsd::enum_loc_side::BOTTOM;
            else
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid node loc side %d.\n", rr_node.side());
        }
        node.loc.ptc = rr_node.ptc_num();
        node.has_timing = true;
        node.timing.R = rr_node.R();
        node.timing.C = rr_node.C();

        int seg_index = device_ctx.rr_indexed_data[rr_node.cost_index()].seg_index;
        if (seg_index != -1) {
            node.has_segment = true;
            node.segment.segment_id = seg_index;
        }

        const auto iter = device_ctx.rr_node_metadata.find(i);
        if (iter != device_ctx.rr_node_metadata.end()) {
            node.has_metadata = true;
            const t_metadata_dict& meta_dict = iter->second;
            for (const auto& meta_elem : meta_dict) {
                const std::string& key = meta_elem.first;
                const std::vector<t_metadata_value>& values = meta_elem.second;
                uxsd::t_meta meta;
                meta.name = key.c_str();
                std::string tmp;
                for (const auto& value : values) {
                    tmp += value.as_string();
                }
                meta.value = uxsd::char_pool.add(tmp.c_str());
                node.metadata.metas.push_back(meta);
            }
        }
        rr_graph.rr_nodes.nodes.push_back(node);
    }
}

/* write_rr_graph_xml helper. */
void write_rr_edges_xml(uxsd::rr_graph& rr_graph) {
    auto& device_ctx = g_vpr_ctx.device();
    int k = 0;
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        auto& rr_node = device_ctx.rr_nodes[i];
        for (t_edge_size j = 0; j < rr_node.num_edges(); j++, k++) {
            uxsd::t_edge edge = {};
            edge.id = k;
            edge.src_node = i;
            edge.sink_node = rr_node.edge_sink_node(j);
            edge.switch_id = rr_node.edge_switch(j);
            auto x = std::make_tuple(i, rr_node.edge_sink_node(j), rr_node.edge_switch(j));
            const auto iter = device_ctx.rr_edge_metadata.find(x);
            if (iter != device_ctx.rr_edge_metadata.end()) {
                edge.has_metadata = true;
                const t_metadata_dict& meta_dict = iter->second;
                for (const auto& meta_elem : meta_dict) {
                    const std::string& key = meta_elem.first;
                    const std::vector<t_metadata_value>& values = meta_elem.second;
                    uxsd::t_meta meta;
                    meta.name = key.c_str();
                    std::string tmp;
                    for (const auto& value : values) {
                        tmp += value.as_string();
                    }
                    meta.value = uxsd::char_pool.add(tmp.c_str());
                    edge.metadata.metas.push_back(meta);
                }
            }
            rr_graph.rr_edges.edges.push_back(edge);
        }
    }
}

/**
 * Copy the VPR structs into a Cap'n Proto message and write it out.
 */
void write_rr_graph_capnp(const char* file_name, const std::vector<t_segment_inf>& segment_inf) {
    auto& device_ctx = g_vpr_ctx.device();
    capnp::MallocMessageBuilder msg;
    ucap::RrGraph::Builder rr_graph = msg.initRoot<ucap::RrGraph>();

    rr_graph.setToolName("vpr");
    rr_graph.setToolVersion(vtr::VERSION);
    std::string tool_comment = std::string("Generated from arch file ") + get_arch_file_name();
    rr_graph.setToolComment(tool_comment.c_str());

    /* Copy channels. */
    auto channels = rr_graph.initChannels();
    auto channel = channels.initChannel();
    channel.setChanWidthMax(device_ctx.chan_width.max);
    channel.setXMin(device_ctx.chan_width.x_min);
    channel.setYMin(device_ctx.chan_width.y_min);
    channel.setXMax(device_ctx.chan_width.x_max);
    channel.setYMax(device_ctx.chan_width.y_max);
    auto x_lists = channels.initXLists(device_ctx.grid.height() - 1);
    for (size_t i = 0; i < device_ctx.grid.height() - 1; i++) {
        auto x_list = x_lists[i];
        x_list.setIndex(i);
        x_list.setInfo(device_ctx.chan_width.x_list[i]);
    }
    auto y_lists = channels.initYLists(device_ctx.grid.width() - 1);
    for (size_t i = 0; i < device_ctx.grid.width() - 1; i++) {
        auto y_list = y_lists[i];
        y_list.setIndex(i);
        y_list.setInfo(device_ctx.chan_width.y_list[i]);
    }

    /* Copy switches. */
    auto switches_parent = rr_graph.initSwitches();
    auto switches = switches_parent.initSwitches(device_ctx.rr_switch_inf.size());
    for (size_t i = 0; i < device_ctx.rr_switch_inf.size(); i++) {
        auto switch_ = switches[i];
        auto& rr_switch = device_ctx.rr_switch_inf[i];
        switch_.setId(i);
        switch_.setName(rr_switch.name);
        auto rr_type = rr_switch.type();
        switch (rr_type) {
            case SwitchType::MUX:
                switch_.setType(ucap::SwitchType::MUX);
                break;
            case SwitchType::TRISTATE:
                switch_.setType(ucap::SwitchType::TRISTATE);
                break;
            case SwitchType::PASS_GATE:
                switch_.setType(ucap::SwitchType::PASS_GATE);
                break;
            case SwitchType::SHORT:
                switch_.setType(ucap::SwitchType::SHORT);
                break;
            case SwitchType::BUFFER:
                switch_.setType(ucap::SwitchType::BUFFER);
                break;
            default:
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid switch type %d.\n", rr_type);
        }
        auto switch_timing = switch_.initTiming();
        switch_timing.setR(rr_switch.R);
        switch_timing.setCin(rr_switch.Cin);
        switch_timing.setCout(rr_switch.Cout);
        switch_timing.setCinternal(rr_switch.Cinternal);
        switch_timing.setTdel(rr_switch.Tdel);
        auto switch_sizing = switch_.initSizing();
        switch_sizing.setMuxTransSize(rr_switch.mux_trans_size);
        switch_sizing.setBufSize(rr_switch.buf_size);
    }

    /* Copy segments. */
    auto segments_parent = rr_graph.initSegments();
    auto segments = segments_parent.initSegments(segment_inf.size());
    for (size_t i = 0; i < segment_inf.size(); i++) {
        auto& rr_segment = segment_inf[i];
        auto segment = segments[i];
        segment.setId(i);
        segment.setName(rr_segment.name.c_str());
        auto segment_timing = segment.initTiming();
        segment_timing.setRPerMeter(rr_segment.Rmetal);
        segment_timing.setCPerMeter(rr_segment.Cmetal);
    }

    /* Copy block types. */
    auto block_types_parent = rr_graph.initBlockTypes();
    auto block_types = block_types_parent.initBlockTypes(device_ctx.physical_tile_types.size());
    for (size_t i=0; i<device_ctx.physical_tile_types.size(); i++) {
        auto& rr_block_type = device_ctx.physical_tile_types[i];
        auto block_type = block_types[i];
        block_type.setId(rr_block_type.index);
        block_type.setName(rr_block_type.name);
        block_type.setWidth(rr_block_type.width);
        block_type.setHeight(rr_block_type.height);
        auto pin_classes = block_type.initPinClasses(rr_block_type.num_class);
        for (int j = 0; j < rr_block_type.num_class; j++) {
            auto& rr_pin_class = rr_block_type.class_inf[j];
            auto pin_class = pin_classes[j];
            if (rr_pin_class.type == -1) {
                pin_class.setType(ucap::PinType::OPEN);
            } else if (rr_pin_class.type == 0) {
                pin_class.setType(ucap::PinType::OUTPUT);
            } else if (rr_pin_class.type == 1) {
                pin_class.setType(ucap::PinType::INPUT);
            } else {
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid pin class type %d.\n", rr_pin_class.type);
            }
            auto pins = pin_class.initPins(rr_pin_class.num_pins);
            for (int k = 0; k < rr_pin_class.num_pins; k++) {
                auto& rr_pin = rr_pin_class.pinlist[k];
                auto pin = pins[k];
                pin.setPtc(rr_pin);
                pin.setValue(block_type_pin_index_to_name(&rr_block_type, rr_pin).c_str());
            }
        }
    }

    /* Copy grid. */
    auto grid = rr_graph.initGrid();
    size_t num_grid_locs = device_ctx.grid.width() * device_ctx.grid.height();
    auto grid_locs = grid.initGridLocs(num_grid_locs);
    for (size_t x = 0; x < device_ctx.grid.width(); x++) {
        for (size_t y = 0; y < device_ctx.grid.height(); y++) {
            auto& rr_grid_loc = device_ctx.grid[x][y];
            auto grid_loc = grid_locs[x + y * device_ctx.grid.width()];
            grid_loc.setX(x);
            grid_loc.setY(y);
            grid_loc.setBlockTypeId(rr_grid_loc.type->index);
            grid_loc.setWidthOffset(rr_grid_loc.width_offset);
            grid_loc.setHeightOffset(rr_grid_loc.height_offset);
        }
    }

    /* Copy nodes and edges. */
    write_rr_nodes_capnp(rr_graph);
    write_rr_edges_capnp(rr_graph);

    /* Write out message. */
    writeMessageToFile(file_name, &msg);
}

void write_rr_nodes_capnp(ucap::RrGraph::Builder& rr_graph) {
    auto& device_ctx = g_vpr_ctx.device();
    auto rr_nodes = rr_graph.initRrNodes();
    auto nodes = rr_nodes.initNodes(device_ctx.rr_nodes.size());
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        auto& rr_node = device_ctx.rr_nodes[i];
        auto node = nodes[i];
        node.setId(i);
        auto type = rr_node.type();
        switch (type) {
            case CHANX:
                node.setType(ucap::NodeType::CHANX);
                break;
            case CHANY:
                node.setType(ucap::NodeType::CHANY);
                break;
            case SOURCE:
                node.setType(ucap::NodeType::SOURCE);
                break;
            case SINK:
                node.setType(ucap::NodeType::SINK);
                break;
            case OPIN:
                node.setType(ucap::NodeType::OPIN);
                break;
            case IPIN:
                node.setType(ucap::NodeType::IPIN);
                break;
            default:
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid node type %d.\n", type);
        }
        if (type == CHANX || type == CHANY) {
            auto direction = rr_node.direction();
            if (direction == INC_DIRECTION) {
                node.setDirection(ucap::NodeDirection::INC_DIR);
            } else if (direction == DEC_DIRECTION) {
                node.setDirection(ucap::NodeDirection::DEC_DIR);
            } else if (direction == BI_DIRECTION) {
                node.setDirection(ucap::NodeDirection::BI_DIR);
            } else {
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid node direction %d.\n", direction);
            }
        }
        node.setCapacity(rr_node.capacity());
        auto loc = node.initLoc();
        loc.setXlow(rr_node.xlow());
        loc.setYlow(rr_node.ylow());
        loc.setXhigh(rr_node.xhigh());
        loc.setYhigh(rr_node.yhigh());
        loc.setPtc(rr_node.ptc_num());
        if (type == IPIN || type == OPIN) {
            auto side = rr_node.side();
            if (side == LEFT) {
                loc.setSide(ucap::LocSide::LEFT);
            } else if (side == RIGHT) {
                loc.setSide(ucap::LocSide::RIGHT);
            } else if (side == TOP) {
                loc.setSide(ucap::LocSide::TOP);
            } else if (side == BOTTOM) {
                loc.setSide(ucap::LocSide::BOTTOM);
            } else {
                VPR_THROW(VPR_ERROR_ROUTE, "Invalid node loc side %d.\n", side);
            }
        }
        auto timing = node.initTiming();
        timing.setR(rr_node.R());
        timing.setC(rr_node.C());
        int seg_index = device_ctx.rr_indexed_data[rr_node.cost_index()].seg_index;
        if (seg_index != -1) {
            auto segment = node.initSegment();
            segment.setSegmentId(seg_index);
        }

        const auto iter = device_ctx.rr_node_metadata.find(i);
        if (iter != device_ctx.rr_node_metadata.end()) {
            const t_metadata_dict& meta_dict = iter->second;
            auto metadata = node.initMetadata();
            auto metas = metadata.initMetas(meta_dict.size());
            int m = 0; /* to index metas */
            for (const auto& meta_elem : meta_dict) {
                const std::string& key = meta_elem.first;
                const std::vector<t_metadata_value>& values = meta_elem.second;
                auto meta = metas[m];
                std::string tmp;
                for (const auto& value : values) {
                    tmp += value.as_string();
                }
                meta.setName(key.c_str());
                meta.setValue(tmp.c_str());
                i++;
            }
        }
    }
}

void write_rr_edges_capnp(ucap::RrGraph::Builder& rr_graph) {
    auto& device_ctx = g_vpr_ctx.device();
    size_t num_edges = 0;
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        num_edges += device_ctx.rr_nodes[i].num_edges();
    }
    auto rr_edges = rr_graph.initRrEdges();
    auto edges = rr_edges.initEdges(num_edges);
    int k = 0; /* to index edges */
    for (size_t i = 0; i < device_ctx.rr_nodes.size(); i++) {
        auto& rr_node = device_ctx.rr_nodes[i];
        for (t_edge_size j = 0; j < rr_node.num_edges(); j++, k++) {
            auto edge = edges[k];
            edge.setId(k);
            edge.setSrcNode(i);
            edge.setSinkNode(rr_node.edge_sink_node(j));
            edge.setSwitchId(rr_node.edge_switch(j));

            auto x = std::make_tuple(i, rr_node.edge_sink_node(j), rr_node.edge_switch(j));
            const auto iter = device_ctx.rr_edge_metadata.find(x);
            if (iter != device_ctx.rr_edge_metadata.end()) {
                const t_metadata_dict& meta_dict = iter->second;
                auto metadata = edge.initMetadata();
                auto metas = metadata.initMetas(meta_dict.size());
                int m = 0; /* to index metas */
                for (const auto& meta_elem : meta_dict) {
                    const std::string& key = meta_elem.first;
                    const std::vector<t_metadata_value>& values = meta_elem.second;
                    auto meta = metas[m];
                    std::string tmp;
                    for (const auto& value : values) {
                        tmp += value.as_string();
                    }
                    meta.setName(key.c_str());
                    meta.setValue(tmp.c_str());
                    m++;
                }
            }
        }
    }
}

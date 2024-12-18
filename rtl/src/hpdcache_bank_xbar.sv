/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : September, 2023
 *  Description   : HPDcache bank crossbar
 *  History       : 2024/11 - C. Fuguet - Add crossbar for multi-bank support
 */
module hpdcache_bank_xbar
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,
    parameter type hpdcache_tag_t        = logic,
    parameter type hpdcache_req_t        = logic,
    parameter type hpdcache_rsp_t        = logic,
    parameter type routing_table_t       = logic,
    parameter int  offStart              = 0,
    parameter int  offWidth              = 0,
    parameter routing_table_t rt         = 0,

    localparam int nReqs  = HPDcacheCfg.u.nRequesters,
    localparam int nBanks = HPDcacheCfg.u.nBanks
)
    //  }}}

    //  Ports
    //  {{{
(
    //      Clock and reset signals
    input  logic                          clk_i,
    input  logic                          rst_ni,

    //      Core request interface
    //         1st cycle
    input  logic                          core_req_valid_i [nReqs],
    output logic                          core_req_ready_o [nReqs],
    input  hpdcache_req_t                 core_req_i       [nReqs],
    //         2nd cycle
    input  logic                          core_req_abort_i [nReqs],
    input  hpdcache_tag_t                 core_req_tag_i   [nReqs],
    input  hpdcache_pma_t                 core_req_pma_i   [nReqs],

    //      Core response interface
    output logic                          core_rsp_valid_o [nReqs],
    input  logic                          core_rsp_ready_i [nReqs],
    output hpdcache_rsp_t                 core_rsp_o       [nReqs],

    //      Bank request (granted request) interface
    //         1st cycle
    output logic                          bank_req_valid_o [nBanks],
    input  logic                          bank_req_ready_i [nBanks],
    output hpdcache_req_t                 bank_req_o       [nBanks],
    //         2nd cycle
    output logic                          bank_abort_o     [nBanks],
    output hpdcache_tag_t                 bank_tag_o       [nBanks],
    output hpdcache_pma_t                 bank_pma_o       [nBanks],

    //      Bank response interface
    input  logic                          bank_rsp_valid_i [nBanks],
    output logic                          bank_rsp_ready_o [nBanks],
    input  hpdcache_rsp_t                 bank_rsp_i       [nBanks]
);
    //  }}}

    //  Declaration of internal constants
    //  {{{
    //  }}}

    //  Declaration of internal signals
    //  {{{
    logic                 [nBanks-1:0][nReqs-1:0]   core_req_valid;
    logic                 [nReqs-1:0][nBanks-1:0]   core_req_ready;
    hpdcache_req_t        [nReqs-1:0]               core_req;
    logic                 [nReqs-1:0]               core_req_abort;
    hpdcache_tag_t        [nReqs-1:0]               core_req_tag;
    hpdcache_pma_t        [nReqs-1:0]               core_req_pma;
    logic                 [nReqs-1:0][offWidth-1:0] core_req_off;
    logic                 [nReqs-1:0][offWidth-1:0] core_req_bid;

    logic                 [nBanks-1:0][nReqs-1:0]   bank_rsp_ready;

    logic [nBanks-1:0][nReqs-1:0] bank_req_gnt_q, bank_req_gnt_d;

    genvar gen_req, gen_bank;
    //  }}}

    //  Requesters arbiter
    //  {{{
    for (gen_req = 0; gen_req < nReqs; gen_req++) begin : gen_core_req_valid
        //  route the request to the indicated bank (routing table)
        assign core_req_off[gen_req]   = core_req_i[gen_req].addr_offset[offStart +: offWidth];
        assign core_req_bid[gen_req]   = nBanks > 1 ? rt[core_req_off[gen_req]] : 0;

        //  pack the input ports
        assign core_req[gen_req]       = core_req_i[gen_req];
        assign core_req_abort[gen_req] = core_req_abort_i[gen_req];
        assign core_req_tag[gen_req]   = core_req_tag_i[gen_req];
        assign core_req_pma[gen_req]   = core_req_pma_i[gen_req];

        for (gen_bank = 0; gen_bank < nBanks; gen_bank++) begin : gen_core_bank_valid
            //  demux valid signal from requesters to banks
            assign core_req_valid[gen_bank][gen_req] =
                    (gen_bank == core_req_bid[gen_req]) & core_req_valid_i[gen_req];

            //  mux ready signal from banks to requesters
            assign core_req_ready[gen_req][gen_bank] =
                    (gen_bank == core_req_bid[gen_req]) & bank_req_ready_i[gen_bank] &
                    bank_req_gnt_d[gen_bank][gen_req];
        end

        //  Logical OR of all ready signals of banks for a given requester
        assign core_req_ready_o[gen_req] = |core_req_ready[gen_req];
    end

    for (gen_bank = 0; gen_bank < nBanks; gen_bank++) begin : gen_bank_arbiter
        //  Arbiter
        hpdcache_fxarb #(.N(nReqs)) req_arbiter_i(
            .clk_i,
            .rst_ni,
            .req_i          (core_req_valid[gen_bank]),
            .gnt_o          (bank_req_gnt_d[gen_bank]),
            .ready_i        (bank_req_ready_i[gen_bank])
        );

        //  Request multiplexor
        hpdcache_mux #(
            .NINPUT         (nReqs),
            .DATA_WIDTH     ($bits(hpdcache_req_t)),
            .ONE_HOT_SEL    (1'b1)
        ) core_req_mux_i(
            .data_i         (core_req),
            .sel_i          (bank_req_gnt_d[gen_bank]),
            .data_o         (bank_req_o[gen_bank])
        );

        //  Request abort multiplexor
        hpdcache_mux #(
            .NINPUT         (nReqs),
            .DATA_WIDTH     (1),
            .ONE_HOT_SEL    (1'b1)
        ) core_req_abort_mux_i(
            .data_i         (core_req_abort),
            .sel_i          (bank_req_gnt_q[gen_bank]),
            .data_o         (bank_abort_o[gen_bank])
        );

        //  Tag Multiplexor
        hpdcache_mux #(
            .NINPUT         (nReqs),
            .DATA_WIDTH     ($bits(hpdcache_tag_t)),
            .ONE_HOT_SEL    (1'b1)
        ) core_req_tag_mux_i(
            .data_i         (core_req_tag),
            .sel_i          (bank_req_gnt_q[gen_bank]),
            .data_o         (bank_tag_o[gen_bank])
        );

        //  PMA Multiplexor
        hpdcache_mux #(
            .NINPUT         (nReqs),
            .DATA_WIDTH     ($bits(hpdcache_pma_t)),
            .ONE_HOT_SEL    (1'b1)
        ) core_req_pma_mux_i(
            .data_i         (core_req_pma),
            .sel_i          (bank_req_gnt_q[gen_bank]),
            .data_o         (bank_pma_o[gen_bank])
        );

        //  Save the grant signal for the tag in the next cycle
        always_ff @(posedge clk_i or negedge rst_ni)
        begin : bank_req_gnt_ff
            if (!rst_ni) bank_req_gnt_q[gen_bank] <= '0;
            else         bank_req_gnt_q[gen_bank] <= bank_req_gnt_d[gen_bank];
        end

        assign bank_req_valid_o[gen_bank] = |bank_req_gnt_d[gen_bank];
        //  }}}
    end

    //  Response arbitration
    //  {{{
    for (gen_req = 0; gen_req < nReqs; gen_req++) begin : gen_req_resp_demux
        logic          [nBanks-1:0] core_rsp_gnt;
        hpdcache_rsp_t [nBanks-1:0] core_rsp;
        logic          [nBanks-1:0] core_rsp_valid;

        //  Response demultiplexor
        for (gen_bank = 0; gen_bank < nBanks; gen_bank++) begin : gen_bank_resp_pack
            assign core_rsp_valid[gen_bank] = bank_rsp_valid_i[gen_bank] &&
                                              (gen_req == int'(bank_rsp_i[gen_bank].sid));
            assign core_rsp[gen_bank] = bank_rsp_i[gen_bank];

            assign bank_rsp_ready[gen_bank][gen_req] = core_rsp_gnt[gen_bank];
        end

        hpdcache_rrarb #(
            .N              (nBanks)
        ) rrarb_rsp_i(
            .clk_i,
            .rst_ni,

            .req_i          (core_rsp_valid),
            .gnt_o          (core_rsp_gnt),
            .ready_i        (core_rsp_ready_i[gen_req])
        );

        hpdcache_mux #(
            .NINPUT         (nBanks),
            .DATA_WIDTH     (1),
            .ONE_HOT_SEL    (1'b1)
        ) core_rsp_valid_mux_i(
            .data_i         (core_rsp_valid),
            .sel_i          (core_rsp_gnt),
            .data_o         (core_rsp_valid_o[gen_req])
        );

        hpdcache_mux #(
            .NINPUT         (nBanks),
            .DATA_WIDTH     ($bits(hpdcache_rsp_t)),
            .ONE_HOT_SEL    (1'b1)
        ) core_rsp_mux_i(
            .data_i         (core_rsp),
            .sel_i          (core_rsp_gnt),
            .data_o         (core_rsp_o[gen_req])
        );
    end

    for (gen_bank = 0; gen_bank < nBanks; gen_bank++) begin : bank_rsp_ready_gen
        assign bank_rsp_ready_o[gen_bank] = |bank_rsp_ready[gen_bank];
    end
    //  }}}
endmodule

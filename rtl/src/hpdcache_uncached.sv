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
 *  Creation Date : May, 2021
 *  Description   : HPDcache uncached and AMO request handler
 *  History       :
 */
module hpdcache_uncached
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_offset_t = logic,
    parameter type hpdcache_word_t = logic,

    parameter type hpdcache_req_addr_t = logic,
    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_be_t = logic,

    parameter type hpdcache_way_vector_t = logic,

    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    parameter type hpdcache_mem_addr_t = logic,
    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic,
    parameter type hpdcache_mem_resp_r_t = logic,
    parameter type hpdcache_mem_resp_w_t = logic,

    parameter type hpdcache_bank_id_t = logic,

    localparam int unsigned nBanks = HPDcacheCfg.u.nBanks
)
    //  }}}

    //  Ports
    //  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //  Global control signals
    //  {{{
    input  logic                  wbuf_empty_i,
    input  logic                  mshr_empty_i,
    input  logic                  refill_busy_i,
    input  logic                  rtab_empty_i,
    input  logic                  ctrl_empty_i,
    input  logic                  flush_empty_i,
    //  }}}

    //  Cache-side request interface
    //  {{{
    input  logic                  req_valid_i    [nBanks],
    output logic                  req_ready_o,
    input  hpdcache_uc_op_t       req_op_i       [nBanks],
    input  hpdcache_req_addr_t    req_addr_i     [nBanks],
    input  hpdcache_req_size_t    req_size_i     [nBanks],
    input  hpdcache_req_data_t    req_data_i     [nBanks],
    input  hpdcache_req_be_t      req_be_i       [nBanks],
    input  logic                  req_uc_i       [nBanks],
    input  hpdcache_req_sid_t     req_sid_i      [nBanks],
    input  hpdcache_req_tid_t     req_tid_i      [nBanks],
    input  logic                  req_need_rsp_i [nBanks],
    //  }}}

    //  Write buffer interface
    //  {{{
    output logic                  wbuf_flush_all_o,
    //  }}}

    //  AMO Cache Interface
    //  {{{
    output logic                  dir_amo_match_o         [nBanks],
    output hpdcache_set_t         dir_amo_match_set_o,
    output hpdcache_tag_t         dir_amo_match_tag_o,
    output logic                  dir_amo_updt_sel_victim_o,
    input  hpdcache_way_vector_t  dir_amo_hit_way_i       [nBanks],

    output logic                  data_amo_write_o        [nBanks],
    output logic                  data_amo_write_enable_o [nBanks],
    output hpdcache_set_t         data_amo_write_set_o,
    output hpdcache_req_size_t    data_amo_write_size_o,
    output hpdcache_word_t        data_amo_write_word_o,
    output hpdcache_req_data_t    data_amo_write_data_o,
    output hpdcache_req_be_t      data_amo_write_be_o,
    // }}}

    //  LR/SC reservation buffer
    //  {{{
    input  logic                  lrsc_snoop_i      [nBanks],
    input  hpdcache_req_addr_t    lrsc_snoop_addr_i [nBanks],
    input  hpdcache_req_size_t    lrsc_snoop_size_i [nBanks],
    //  }}}

    //  Core response interface
    //  {{{
    input  logic                  core_rsp_ready_i [nBanks],
    output logic                  core_rsp_valid_o [nBanks],
    output hpdcache_rsp_t         core_rsp_o,
    //  }}}

    //  MEMORY interfaces
    //  {{{
    //      Memory request unique identifier
    input  hpdcache_mem_id_t      mem_read_id_i,
    input  hpdcache_mem_id_t      mem_write_id_i,

    //      Read interface
    input  logic                  mem_req_read_ready_i,
    output logic                  mem_req_read_valid_o,
    output hpdcache_mem_req_t     mem_req_read_o,

    output logic                  mem_resp_read_ready_o,
    input  logic                  mem_resp_read_valid_i,
    input  hpdcache_mem_resp_r_t  mem_resp_read_i,

    //      Write interface
    input  logic                  mem_req_write_ready_i,
    output logic                  mem_req_write_valid_o,
    output hpdcache_mem_req_t     mem_req_write_o,

    input  logic                  mem_req_write_data_ready_i,
    output logic                  mem_req_write_data_valid_o,
    output hpdcache_mem_req_w_t   mem_req_write_data_o,

    output logic                  mem_resp_write_ready_o,
    input  logic                  mem_resp_write_valid_i,
    input  hpdcache_mem_resp_w_t  mem_resp_write_i,
    //  }}}

    //  Configuration interface
    //  {{{
    input  logic                  cfg_error_on_cacheable_amo_i
    //  }}}
);
    //  }}}

//  Definition of constants and types
//  {{{
    localparam hpdcache_uint MEM_REQ_RATIO = HPDcacheCfg.u.memDataWidth/HPDcacheCfg.reqDataWidth;
    localparam hpdcache_uint MEM_REQ_WORD_INDEX_WIDTH = $clog2(MEM_REQ_RATIO);

    typedef struct packed {
        hpdcache_uc_op_t    op;
        hpdcache_req_addr_t addr;
        hpdcache_req_size_t size;
        hpdcache_req_data_t data;
        hpdcache_req_be_t   be;
        logic               uc;
        hpdcache_req_sid_t  sid;
        hpdcache_req_tid_t  tid;
        logic               need_rsp;
        hpdcache_bank_id_t           bank_id;
    } uc_req_t;

    typedef enum {
        UC_IDLE,
        UC_WAIT_PENDING,
        UC_MEM_REQ,
        UC_MEM_W_REQ,
        UC_MEM_WDATA_REQ,
        UC_MEM_WAIT_RSP,
        UC_CORE_RSP,
        UC_AMO_READ_DIR,
        UC_AMO_WRITE_DATA
    } hpdcache_uc_fsm_t;

    localparam logic AMO_SC_SUCCESS = 1'b0;
    localparam logic AMO_SC_FAILURE = 1'b1;

    function automatic logic [63:0] prepare_amo_data_operand(
            input logic [63:0]        data_i,
            input hpdcache_req_size_t size_i,
            input hpdcache_req_addr_t addr_i,
            input logic               sign_extend_i
    );
        // 64-bits AMOs are already aligned, thus do nothing
        if (size_i == hpdcache_req_size_t'(3)) begin
            return data_i;
        end

        // 32-bits AMOs
        else begin
            if (addr_i[2] == 1'b1) begin
                if (sign_extend_i) begin
                    return {{32{data_i[63]}}, data_i[63:32]};
                end else begin
                    return {{32{      1'b0}}, data_i[63:32]};
                end
            end else begin
                if (sign_extend_i) begin
                    return {{32{data_i[31]}}, data_i[31: 0]};
                end else begin
                    return {{32{      1'b0}}, data_i[31: 0]};
                end
            end
        end
    endfunction;

    function automatic logic [63:0] prepare_amo_data_result(
            input logic [63:0]        data_i,
            input hpdcache_req_size_t size_i
    );
        // 64-bits AMOs are already aligned, thus do nothing
        if (size_i == hpdcache_req_size_t'(3)) begin
            return data_i;
        end

        // 32-bits AMOs
        else begin
            return {2{data_i[31:0]}};
        end
    endfunction;

    function automatic logic amo_need_sign_extend(hpdcache_uc_op_t op);
        unique case (1'b1)
            op.is_amo_add,
            op.is_amo_max,
            op.is_amo_min: return 1'b1;
            default      : return 1'b0;
        endcase;
    endfunction
//  }}}

//  Internal signals and registers
//  {{{
    logic [nBanks-1:0]    arb_req_valid;
    logic [nBanks-1:0]    arb_req_gnt;
    logic                 arb_ready;
    logic                 arb_valid;
    uc_req_t [nBanks-1:0] core_req;
    uc_req_t              arb_req;

    hpdcache_uc_fsm_t   uc_fsm_q, uc_fsm_d;
    uc_req_t            req_q;
    logic               no_pend_trans;

    logic               uc_sc_retcode_q, uc_sc_retcode_d;

    hpdcache_req_data_t rsp_rdata_q, rsp_rdata_d;
    logic               rsp_error_set, rsp_error_rst;
    logic               rsp_error_q;
    logic               mem_resp_write_valid_q, mem_resp_write_valid_d;
    logic               mem_resp_read_valid_q, mem_resp_read_valid_d;

    hpdcache_req_data_t mem_req_write_data;
    logic [63:0]        amo_req_ld_data;
    logic [63:0]        amo_ld_data;
    logic [63:0]        amo_req_st_data;
    logic [63:0]        amo_st_data;
    logic [63:0]        amo_result;
    logic [63:0]        amo_write_data;
//  }}}

//  LR/SC reservation buffer logic
//  {{{
    logic               lrsc_rsrv_valid_q;
    hpdcache_req_addr_t lrsc_rsrv_addr_q, lrsc_rsrv_addr_d;
    hpdcache_nline_t    lrsc_rsrv_nline;
    hpdcache_offset_t   lrsc_rsrv_word;

    hpdcache_offset_t   lrsc_snoop_words [nBanks];
    hpdcache_nline_t    lrsc_snoop_nline [nBanks];
    hpdcache_offset_t   lrsc_snoop_base [nBanks];
    hpdcache_offset_t   lrsc_snoop_end [nBanks];
    logic [nBanks-1:0]  lrsc_snoop_hit;
    logic               lrsc_snoop_reset;

    hpdcache_nline_t    lrsc_uc_nline;
    hpdcache_offset_t   lrsc_uc_word;
    logic               lrsc_uc_hit;
    logic               lrsc_uc_set, lrsc_uc_reset;

    //  NOTE: Reservation set for LR instruction is always 8-bytes in this
    //  implementation.
    assign lrsc_rsrv_nline  = lrsc_rsrv_addr_q[HPDcacheCfg.clOffsetWidth +:
                                               HPDcacheCfg.nlineWidth];
    assign lrsc_rsrv_word   = lrsc_rsrv_addr_q[0 +: HPDcacheCfg.clOffsetWidth] >> 3;

    //  Check hit on LR/SC reservation for snoop port (normal write accesses)
    generate
    genvar gen_snoop;
    for (gen_snoop = 0; gen_snoop < nBanks; gen_snoop++) begin : gen_snoop_hit
        assign lrsc_snoop_words[gen_snoop] = (lrsc_snoop_size_i[gen_snoop] < 3) ?
                1 : hpdcache_offset_t'((8'h1 << lrsc_snoop_size_i[gen_snoop]) >> 3);
        assign lrsc_snoop_nline[gen_snoop] = lrsc_snoop_addr_i[gen_snoop][HPDcacheCfg.clOffsetWidth +:
                                                    HPDcacheCfg.nlineWidth];
        assign lrsc_snoop_base[gen_snoop]  = lrsc_snoop_addr_i[gen_snoop][0 +: HPDcacheCfg.clOffsetWidth] >> 3;
        assign lrsc_snoop_end[gen_snoop]   = lrsc_snoop_base[gen_snoop] + lrsc_snoop_words[gen_snoop];

        assign lrsc_snoop_hit[gen_snoop]   = lrsc_rsrv_valid_q & lrsc_snoop_i[gen_snoop] &
                                                    (lrsc_rsrv_nline == lrsc_snoop_nline[gen_snoop]) &
                                                    (lrsc_rsrv_word  >= lrsc_snoop_base[gen_snoop]) &
                                                    (lrsc_rsrv_word  <  lrsc_snoop_end[gen_snoop] );
    end
    endgenerate

    assign lrsc_snoop_reset =  |lrsc_snoop_hit;

    //  Check hit on LR/SC reservation for AMOs and SC
    assign lrsc_uc_nline    = arb_req.addr[HPDcacheCfg.clOffsetWidth +: HPDcacheCfg.nlineWidth];
    assign lrsc_uc_word     = arb_req.addr[0 +: HPDcacheCfg.clOffsetWidth] >> 3;

    assign lrsc_uc_hit      = lrsc_rsrv_valid_q & (lrsc_rsrv_nline == lrsc_uc_nline) &
                                                  (lrsc_rsrv_word  == lrsc_uc_word);
//  }}}

    assign no_pend_trans = wbuf_empty_i &&
                           mshr_empty_i &&
                           ~refill_busy_i &&
                           rtab_empty_i &&
                           ctrl_empty_i &&
                           flush_empty_i;

//  Bank request mux
//  {{{
    generate
        genvar gen_req;
        for (gen_req = 0; gen_req < nBanks; gen_req++) begin : gen_core_req
            // Pack inputs
            assign arb_req_valid[gen_req] = req_valid_i[gen_req];
            assign core_req[gen_req] = '{
                op:       req_op_i[gen_req],
                addr:     req_addr_i[gen_req],
                size:     req_size_i[gen_req],
                data:     req_data_i[gen_req],
                be:       req_be_i[gen_req],
                uc:       req_uc_i[gen_req],
                sid:      req_sid_i[gen_req],
                tid:      req_tid_i[gen_req],
                need_rsp: req_need_rsp_i[gen_req],
                bank_id:  gen_req
            };
        end
    endgenerate

    assign arb_ready = uc_fsm_q == UC_IDLE;
    assign req_ready_o = arb_ready;
    assign arb_valid = |arb_req_gnt;

    hpdcache_fxarb #(.N(nBanks)) req_arbiter_i(
        .clk_i,
        .rst_ni,
        .req_i          (arb_req_valid),
        .gnt_o          (arb_req_gnt),
        .ready_i        (arb_ready)
    );

    //  Request multiplexor
    hpdcache_mux #(
        .NINPUT         (nBanks),
        .DATA_WIDTH     ($bits(uc_req_t)),
        .ONE_HOT_SEL    (1'b1)
    ) core_req_mux_i(
        .data_i         (core_req),
        .sel_i          (arb_req_gnt),
        .data_o         (arb_req)
    );

//  }}}

//  Uncacheable request FSM
//  {{{
    always_comb
    begin : uc_fsm_comb
        mem_resp_write_valid_d = mem_resp_write_valid_q;
        mem_resp_read_valid_d  = mem_resp_read_valid_q;
        rsp_error_set          = 1'b0;
        rsp_error_rst          = 1'b0;
        lrsc_rsrv_addr_d       = lrsc_rsrv_addr_q;
        uc_sc_retcode_d        = uc_sc_retcode_q;
        wbuf_flush_all_o       = 1'b0;
        lrsc_uc_set            = 1'b0;
        lrsc_uc_reset          = 1'b0;

        uc_fsm_d               = uc_fsm_q;

        unique case (uc_fsm_q)
            //  Wait for a request
            //  {{{
            UC_IDLE: begin

                if (arb_valid) begin
                    wbuf_flush_all_o = 1'b1;

                    unique case (1'b1)
                        arb_req.op.is_ld,
                        arb_req.op.is_st: begin
                            if (no_pend_trans) begin
                                uc_fsm_d = UC_MEM_REQ;
                            end else begin
                                uc_fsm_d = UC_WAIT_PENDING;
                            end
                        end

                        arb_req.op.is_amo_swap,
                        arb_req.op.is_amo_add,
                        arb_req.op.is_amo_and,
                        arb_req.op.is_amo_or,
                        arb_req.op.is_amo_xor,
                        arb_req.op.is_amo_max,
                        arb_req.op.is_amo_maxu,
                        arb_req.op.is_amo_min,
                        arb_req.op.is_amo_minu,
                        arb_req.op.is_amo_lr: begin
                            //  Reset LR/SC reservation if AMO matches its address
                            lrsc_uc_reset = ~arb_req.op.is_amo_lr & lrsc_uc_hit;

                            if (!arb_req.uc && cfg_error_on_cacheable_amo_i) begin
                                rsp_error_set = 1'b1;
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                if (no_pend_trans) begin
                                    uc_fsm_d = UC_MEM_REQ;
                                end else begin
                                    uc_fsm_d = UC_WAIT_PENDING;
                                end
                            end
                        end

                        arb_req.op.is_amo_sc: begin
                            if (!arb_req.uc && cfg_error_on_cacheable_amo_i) begin
                                rsp_error_set = 1'b1;
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                //  Reset previous reservation (if any)
                                lrsc_uc_reset = 1'b1;

                                //  SC with valid reservation
                                if (lrsc_uc_hit) begin
                                    if (no_pend_trans) begin
                                        uc_fsm_d = UC_MEM_REQ;
                                    end else begin
                                        uc_fsm_d = UC_WAIT_PENDING;
                                    end
                                end
                                //  SC with no valid reservation, thus respond with the failure code
                                else begin
                                    uc_sc_retcode_d = AMO_SC_FAILURE;
                                    uc_fsm_d = UC_CORE_RSP;
                                end
                            end
                        end

                        default: begin
                            if (arb_req.need_rsp) begin
                                rsp_error_set = 1'b1;
                                uc_fsm_d = UC_CORE_RSP;
                            end
                        end
                    endcase
                end
            end
            //  }}}

            //  Wait for all pending transactions to be completed
            //  {{{
            UC_WAIT_PENDING: begin
                if (no_pend_trans) begin
                    uc_fsm_d = UC_MEM_REQ;
                end else begin
                    uc_fsm_d = UC_WAIT_PENDING;
                end
            end
            //  }}}

            //  Send request to memory
            //  {{{
            UC_MEM_REQ: begin
                uc_fsm_d = UC_MEM_REQ;

                mem_resp_write_valid_d = 1'b0;
                mem_resp_read_valid_d  = 1'b0;

                unique case (1'b1)
                    req_q.op.is_ld,
                    req_q.op.is_amo_lr: begin
                        if (mem_req_read_ready_i) begin
                            uc_fsm_d = UC_MEM_WAIT_RSP;
                        end
                    end

                    req_q.op.is_st,
                    req_q.op.is_amo_sc,
                    req_q.op.is_amo_swap,
                    req_q.op.is_amo_add,
                    req_q.op.is_amo_and,
                    req_q.op.is_amo_or,
                    req_q.op.is_amo_xor,
                    req_q.op.is_amo_max,
                    req_q.op.is_amo_maxu,
                    req_q.op.is_amo_min,
                    req_q.op.is_amo_minu: begin
                        if (mem_req_write_ready_i && mem_req_write_data_ready_i) begin
                            uc_fsm_d = UC_MEM_WAIT_RSP;
                        end else if (mem_req_write_ready_i) begin
                            uc_fsm_d = UC_MEM_WDATA_REQ;
                        end else if (mem_req_write_data_ready_i) begin
                            uc_fsm_d = UC_MEM_W_REQ;
                        end
                    end
                endcase
            end
            //  }}}

            //  Send write address
            //  {{{
            UC_MEM_W_REQ: begin
                mem_resp_write_valid_d = mem_resp_write_valid_q | mem_resp_write_valid_i;
                mem_resp_read_valid_d  =  mem_resp_read_valid_q |  mem_resp_read_valid_i;

                if (mem_req_write_ready_i) begin
                    uc_fsm_d = UC_MEM_WAIT_RSP;
                end else begin
                    uc_fsm_d = UC_MEM_W_REQ;
                end
            end
            //  }}}

            //  Send write data
            //  {{{
            UC_MEM_WDATA_REQ: begin
                mem_resp_write_valid_d = mem_resp_write_valid_q | mem_resp_write_valid_i;
                mem_resp_read_valid_d  =  mem_resp_read_valid_q |  mem_resp_read_valid_i;

                if (mem_req_write_data_ready_i) begin
                    uc_fsm_d = UC_MEM_WAIT_RSP;
                end else begin
                    uc_fsm_d = UC_MEM_WDATA_REQ;
                end
            end
            //  }}}

            //  Wait for the response from the memory
            //  {{{
            UC_MEM_WAIT_RSP: begin
                automatic bit rd_error;
                automatic bit wr_error;

                uc_fsm_d = UC_MEM_WAIT_RSP;
                mem_resp_write_valid_d = mem_resp_write_valid_q | mem_resp_write_valid_i;
                mem_resp_read_valid_d  =  mem_resp_read_valid_q |  mem_resp_read_valid_i;

                rd_error = mem_resp_read_valid_i  &&
                           ( mem_resp_read_i.mem_resp_r_error == HPDCACHE_MEM_RESP_NOK);
                wr_error = mem_resp_write_valid_i &&
                           (mem_resp_write_i.mem_resp_w_error == HPDCACHE_MEM_RESP_NOK);
                rsp_error_set = req_q.need_rsp & (rd_error | wr_error);

                unique case (1'b1)
                    req_q.op.is_ld: begin
                        if (mem_resp_read_valid_i) begin
                            if (req_q.need_rsp) begin
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                uc_fsm_d = UC_IDLE;
                            end
                        end
                    end
                    req_q.op.is_st: begin
                        if (mem_resp_write_valid_i) begin
                            if (req_q.need_rsp) begin
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                uc_fsm_d = UC_IDLE;
                            end
                        end
                    end
                    req_q.op.is_amo_lr: begin
                        if (mem_resp_read_valid_i) begin
                            //  set a new reservation
                            if (!rd_error)
                            begin
                                lrsc_uc_set      = 1'b1;
                                lrsc_rsrv_addr_d = req_q.addr;
                            end
                            //  in case of a memory error, do not make the reservation and
                            //  invalidate an existing one (if valid)
                            else begin
                                lrsc_uc_reset = 1'b1;
                            end

                            if (req_q.uc || rd_error) begin
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                uc_fsm_d = UC_AMO_READ_DIR;
                            end
                        end
                    end
                    req_q.op.is_amo_sc: begin
                        if (mem_resp_write_valid_i) begin
                            automatic bit is_atomic;

                            is_atomic = mem_resp_write_i.mem_resp_w_is_atomic && !wr_error;
                            uc_sc_retcode_d = is_atomic ? AMO_SC_SUCCESS : AMO_SC_FAILURE;

                            if (req_q.uc || !is_atomic) begin
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                uc_fsm_d = UC_AMO_READ_DIR;
                            end
                        end
                    end
                    req_q.op.is_amo_swap,
                    req_q.op.is_amo_add,
                    req_q.op.is_amo_and,
                    req_q.op.is_amo_or,
                    req_q.op.is_amo_xor,
                    req_q.op.is_amo_max,
                    req_q.op.is_amo_maxu,
                    req_q.op.is_amo_min,
                    req_q.op.is_amo_minu: begin
                        //  wait for both old data and write acknowledged were received
                        if ((mem_resp_read_valid_i && mem_resp_write_valid_i) ||
                            (mem_resp_read_valid_i && mem_resp_write_valid_q) ||
                            (mem_resp_read_valid_q && mem_resp_write_valid_i))
                        begin
                            if (req_q.uc || rsp_error_q || rd_error || wr_error) begin
                                uc_fsm_d = UC_CORE_RSP;
                            end else begin
                                uc_fsm_d = UC_AMO_READ_DIR;
                            end
                        end
                    end
                endcase
            end
            //  }}}

            //  Send the response to the requester
            //  {{{
            UC_CORE_RSP: begin
                if (core_rsp_ready_i[req_q.bank_id]) begin
                    rsp_error_rst = 1'b1;
                    uc_fsm_d = UC_IDLE;
                end else begin
                    uc_fsm_d = UC_CORE_RSP;
                end
            end
            //  }}}

            //  Check for a cache hit on the AMO target address
            //  {{{
            UC_AMO_READ_DIR: begin
                uc_fsm_d = UC_AMO_WRITE_DATA;
            end
            //  }}}

            //  Write the locally computed AMO result in the cache
            //  {{{
            UC_AMO_WRITE_DATA: begin
                uc_fsm_d = UC_CORE_RSP;
            end
            //  }}}
        endcase
    end
//  }}}

//  AMO unit
//  {{{
    if (HPDcacheCfg.reqDataWidth > 64) begin : gen_amo_data_width_gt_64
        localparam hpdcache_uint AMO_WORD_INDEX_WIDTH = $clog2(HPDcacheCfg.reqDataWidth/64);
        hpdcache_mux #(
            .NINPUT         (HPDcacheCfg.reqDataWidth/64),
            .DATA_WIDTH     (64),
            .ONE_HOT_SEL    (1'b0)
        ) amo_ld_data_mux_i (
            .data_i         (rsp_rdata_q),
            .sel_i          (req_q.addr[3 +: AMO_WORD_INDEX_WIDTH]),
            .data_o         (amo_req_ld_data)
        );

        hpdcache_mux #(
            .NINPUT         (HPDcacheCfg.reqDataWidth/64),
            .DATA_WIDTH     (64),
            .ONE_HOT_SEL    (1'b0)
        ) amo_st_data_mux_i (
            .data_i         (req_q.data),
            .sel_i          (req_q.addr[3 +: AMO_WORD_INDEX_WIDTH]),
            .data_o         (amo_req_st_data)
        );
    end else if (HPDcacheCfg.reqDataWidth == 64) begin : gen_amo_data_width_eq_64
        assign amo_req_ld_data = rsp_rdata_q;
        assign amo_req_st_data = req_q.data;
    end else begin : gen_amo_data_width_eq_32
        assign amo_req_ld_data = req_q.addr[2] ? {rsp_rdata_q, 32'b0} : {32'b0, rsp_rdata_q};
        assign amo_req_st_data = req_q.addr[2] ? {req_q.data, 32'b0} : {32'b0, req_q.data};
    end

    assign amo_ld_data = prepare_amo_data_operand(amo_req_ld_data, req_q.size,
            req_q.addr, amo_need_sign_extend(req_q.op));
    assign amo_st_data = prepare_amo_data_operand(amo_req_st_data, req_q.size,
            req_q.addr, amo_need_sign_extend(req_q.op));

    hpdcache_amo amo_unit_i (
        .ld_data_i           (amo_ld_data),
        .st_data_i           (amo_st_data),
        .op_i                (req_q.op),
        .result_o            (amo_result)
    );

    generate
        genvar gen_bank_ctrl;
        for (gen_bank_ctrl = 0; gen_bank_ctrl < nBanks; gen_bank_ctrl++) begin : gen_bank_ctrl_signals
            assign dir_amo_match_o[gen_bank_ctrl] = (uc_fsm_q == UC_AMO_READ_DIR) && (req_q.bank_id == gen_bank_ctrl);
            assign data_amo_write_o[gen_bank_ctrl] = (uc_fsm_q == UC_AMO_WRITE_DATA) && (req_q.bank_id == gen_bank_ctrl);
            assign data_amo_write_enable_o[gen_bank_ctrl] = |dir_amo_hit_way_i[gen_bank_ctrl];
        end
    endgenerate

    assign dir_amo_match_set_o = req_q.addr[HPDcacheCfg.clOffsetWidth +: HPDcacheCfg.setWidth];
    assign dir_amo_match_tag_o = req_q.addr[(HPDcacheCfg.clOffsetWidth + HPDcacheCfg.setWidth) +:
                                            HPDcacheCfg.tagWidth];
    assign dir_amo_updt_sel_victim_o = (uc_fsm_q == UC_AMO_WRITE_DATA);

    assign data_amo_write_set_o = req_q.addr[HPDcacheCfg.clOffsetWidth +: HPDcacheCfg.setWidth];
    assign data_amo_write_size_o = req_q.size;
    assign data_amo_write_word_o = req_q.addr[HPDcacheCfg.wordByteIdxWidth +:
                                              HPDcacheCfg.clWordIdxWidth];
    assign data_amo_write_be_o = req_q.be;

    assign amo_write_data = prepare_amo_data_result(amo_result, req_q.size);
    if (HPDcacheCfg.reqDataWidth >= 64) begin : gen_amo_ram_write_data_ge_64
        assign data_amo_write_data_o = {HPDcacheCfg.reqDataWidth/64{amo_write_data}};
    end else begin : gen_amo_ram_write_data_lt_64
        assign data_amo_write_data_o = amo_write_data;
    end
//  }}}

//  Core response outputs
//  {{{

    generate
        genvar gen_core_rsp;
        for (gen_core_rsp = 0; gen_core_rsp < nBanks; gen_core_rsp++) begin : gen_core_rsp_valid
            assign core_rsp_valid_o[gen_core_rsp] = (uc_fsm_q == UC_CORE_RSP) && (req_q.bank_id == gen_core_rsp);
        end
    endgenerate
//  }}}

//  Memory read request outputs
//  {{{
    always_comb
    begin : mem_req_read_comb
        mem_req_read_o.mem_req_addr      = hpdcache_mem_addr_t'(req_q.addr);
        mem_req_read_o.mem_req_len       = 0;
        mem_req_read_o.mem_req_size      = req_q.size;
        mem_req_read_o.mem_req_id        = mem_read_id_i;
        mem_req_read_o.mem_req_cacheable = 1'b0;
        mem_req_read_o.mem_req_command   = HPDCACHE_MEM_READ;
        mem_req_read_o.mem_req_atomic    = HPDCACHE_MEM_ATOMIC_ADD;

        unique case (1'b1)
            req_q.op.is_ld: begin
                mem_req_read_valid_o           = (uc_fsm_q == UC_MEM_REQ);
            end
            req_q.op.is_amo_lr: begin
                mem_req_read_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_read_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_LDEX;
                mem_req_read_valid_o           = (uc_fsm_q == UC_MEM_REQ);
            end
            default: begin
                mem_req_read_valid_o           = 1'b0;
            end
        endcase
    end
//  }}}

//  Memory write request outputs
//  {{{
    always_comb
    begin : mem_req_write_comb
        mem_req_write_data                = req_q.data;
        mem_req_write_o.mem_req_addr      = hpdcache_mem_addr_t'(req_q.addr);
        mem_req_write_o.mem_req_len       = 0;
        mem_req_write_o.mem_req_size      = req_q.size;
        mem_req_write_o.mem_req_id        = mem_write_id_i;
        mem_req_write_o.mem_req_cacheable = 1'b0;
        unique case (1'b1)
            req_q.op.is_amo_sc: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_STEX;
            end
            req_q.op.is_amo_swap: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_SWAP;
            end
            req_q.op.is_amo_add: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_ADD;
            end
            req_q.op.is_amo_and: begin
                mem_req_write_data              = ~req_q.data;
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_CLR;
            end
            req_q.op.is_amo_or: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_SET;
            end
            req_q.op.is_amo_xor: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_EOR;
            end
            req_q.op.is_amo_max: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_SMAX;
            end
            req_q.op.is_amo_maxu: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_UMAX;
            end
            req_q.op.is_amo_min: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_SMIN;
            end
            req_q.op.is_amo_minu: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_ATOMIC;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_UMIN;
            end
            default: begin
                mem_req_write_o.mem_req_command = HPDCACHE_MEM_WRITE;
                mem_req_write_o.mem_req_atomic  = HPDCACHE_MEM_ATOMIC_ADD;
            end
        endcase

        unique case (uc_fsm_q)
            UC_MEM_REQ: begin
                unique case (1'b1)
                    req_q.op.is_st,
                    req_q.op.is_amo_sc,
                    req_q.op.is_amo_swap,
                    req_q.op.is_amo_add,
                    req_q.op.is_amo_and,
                    req_q.op.is_amo_or,
                    req_q.op.is_amo_xor,
                    req_q.op.is_amo_max,
                    req_q.op.is_amo_maxu,
                    req_q.op.is_amo_min,
                    req_q.op.is_amo_minu: begin
                        mem_req_write_data_valid_o = 1'b1;
                        mem_req_write_valid_o      = 1'b1;
                    end

                    default: begin
                        mem_req_write_data_valid_o = 1'b0;
                        mem_req_write_valid_o      = 1'b0;
                    end
                endcase
            end

            UC_MEM_W_REQ: begin
                mem_req_write_valid_o      = 1'b1;
                mem_req_write_data_valid_o = 1'b0;
            end

            UC_MEM_WDATA_REQ: begin
                mem_req_write_valid_o      = 1'b0;
                mem_req_write_data_valid_o = 1'b1;
            end

            default: begin
                mem_req_write_valid_o      = 1'b0;
                mem_req_write_data_valid_o = 1'b0;
            end
        endcase
    end

    //  memory data width is bigger than the width of the core's interface
    if (MEM_REQ_RATIO > 1) begin : gen_upsize_mem_req_data
        //  replicate data
        assign mem_req_write_data_o.mem_req_w_data = {MEM_REQ_RATIO{mem_req_write_data}};

        //  demultiplex the byte-enable
        hpdcache_demux #(
            .NOUTPUT     (MEM_REQ_RATIO),
            .DATA_WIDTH  (HPDcacheCfg.reqDataWidth/8)
        ) mem_write_be_demux_i (
            .data_i      (req_q.be),
            .sel_i       (req_q.addr[$clog2(HPDcacheCfg.reqDataWidth/8) +:
                                     MEM_REQ_WORD_INDEX_WIDTH]),
            .data_o      (mem_req_write_data_o.mem_req_w_be)
        );
    end

    //  memory data width is equal to the width of the core's interface
    else begin : gen_eqsize_mem_req_data
        assign mem_req_write_data_o.mem_req_w_data = mem_req_write_data;
        assign mem_req_write_data_o.mem_req_w_be   = req_q.be;
    end

    assign mem_req_write_data_o.mem_req_w_last = 1'b1;
//  }}}

//  Response handling
//  {{{
    logic [63:0]        sc_retcode;
    logic [63:0]        sc_rdata_dword;
    hpdcache_req_data_t sc_rdata;

    assign sc_retcode = {{63{1'b0}}, uc_sc_retcode_q};
    assign sc_rdata_dword = prepare_amo_data_result(sc_retcode, req_q.size);
    if (HPDcacheCfg.reqDataWidth >= 64) begin : gen_sc_rdata_ge_64
        assign sc_rdata = {HPDcacheCfg.reqDataWidth/64{sc_rdata_dword}};
    end else begin : gen_sc_rdata_lt_64
        assign sc_rdata = sc_rdata_dword;
    end

    assign core_rsp_o.rdata   = req_q.op.is_amo_sc ? sc_rdata : rsp_rdata_q;
    assign core_rsp_o.sid     = req_q.sid;
    assign core_rsp_o.tid     = req_q.tid;
    assign core_rsp_o.error   = rsp_error_q;
    assign core_rsp_o.aborted = 1'b0;

    //  Resize the memory response data to the core response width
    //  memory data width is bigger than the width of the core's interface
    if (MEM_REQ_RATIO > 1) begin : gen_downsize_core_rsp_data
        hpdcache_mux #(
            .NINPUT      (MEM_REQ_RATIO),
            .DATA_WIDTH  (HPDcacheCfg.reqDataWidth)
        ) data_read_rsp_mux_i(
            .data_i      (mem_resp_read_i.mem_resp_r_data),
            .sel_i       (req_q.addr[$clog2(HPDcacheCfg.reqDataWidth/8) +:
                                     MEM_REQ_WORD_INDEX_WIDTH]),
            .data_o      (rsp_rdata_d)
        );
    end

    //  memory data width is equal to the width of the core's interface
    else begin : gen_eqsize_core_rsp_data
        assign rsp_rdata_d = mem_resp_read_i.mem_resp_r_data;
    end

    //  This FSM is always ready to accept the response
    assign mem_resp_read_ready_o  = 1'b1,
           mem_resp_write_ready_o = 1'b1;
//  }}}

//  Set cache request registers
//  {{{
    always_ff @(posedge clk_i)
    begin : req_ff
        if (arb_valid && arb_ready) begin
            req_q <= arb_req;
        end
    end
//  }}}

//  Uncacheable request FSM set state
//  {{{
    logic lrsc_rsrv_valid_set, lrsc_rsrv_valid_reset;

    assign lrsc_rsrv_valid_set   = lrsc_uc_set,
           lrsc_rsrv_valid_reset = lrsc_uc_reset | lrsc_snoop_reset;

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : uc_fsm_ff
        if (!rst_ni) begin
            uc_fsm_q          <= UC_IDLE;
            lrsc_rsrv_valid_q <= 1'b0;
        end else begin
            uc_fsm_q          <= uc_fsm_d;
            lrsc_rsrv_valid_q <= (~lrsc_rsrv_valid_q &  lrsc_rsrv_valid_set  ) |
                                 ( lrsc_rsrv_valid_q & ~lrsc_rsrv_valid_reset);
        end
    end

    always_ff @(posedge clk_i)
    begin : uc_amo_ff
        lrsc_rsrv_addr_q <= lrsc_rsrv_addr_d;
        uc_sc_retcode_q  <= uc_sc_retcode_d;
    end
//  }}}

//  Response registers
//  {{{
    always_ff @(posedge clk_i)
    begin
        if (mem_resp_read_valid_i) begin
            rsp_rdata_q <= rsp_rdata_d;
        end
        mem_resp_write_valid_q <= mem_resp_write_valid_d;
        mem_resp_read_valid_q  <= mem_resp_read_valid_d;
    end

    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            rsp_error_q <= 1'b0;
        end else begin
            rsp_error_q <= (~rsp_error_q &  rsp_error_set) |
                           ( rsp_error_q & ~rsp_error_rst);
        end
    end
//  }}}

//  Assertions
//  {{{
`ifndef HPDCACHE_ASSERT_OFF
    assert property (@(posedge clk_i) disable iff (!rst_ni)
            (arb_valid && arb_req.op.is_ld) -> arb_req.uc) else
                    $error("uc_handler: unexpected load request on cacheable region");

    assert property (@(posedge clk_i) disable iff (!rst_ni)
            (arb_valid && arb_req.op.is_st) -> arb_req.uc) else
                    $error("uc_handler: unexpected store request on cacheable region");

    assert property (@(posedge clk_i) disable iff (!rst_ni)
            (arb_valid && (arb_req.op.is_amo_lr   ||
                             arb_req.op.is_amo_sc   ||
                             arb_req.op.is_amo_swap ||
                             arb_req.op.is_amo_add  ||
                             arb_req.op.is_amo_and  ||
                             arb_req.op.is_amo_or   ||
                             arb_req.op.is_amo_xor  ||
                             arb_req.op.is_amo_max  ||
                             arb_req.op.is_amo_maxu ||
                             arb_req.op.is_amo_min  ||
                             arb_req.op.is_amo_minu )) -> arb_req.need_rsp) else
                    $error("uc_handler: amo requests shall need a response");

    assert property (@(posedge clk_i) disable iff (!rst_ni)
            (arb_valid && (arb_req.op.is_amo_lr   ||
                             arb_req.op.is_amo_sc   ||
                             arb_req.op.is_amo_swap ||
                             arb_req.op.is_amo_add  ||
                             arb_req.op.is_amo_and  ||
                             arb_req.op.is_amo_or   ||
                             arb_req.op.is_amo_xor  ||
                             arb_req.op.is_amo_max  ||
                             arb_req.op.is_amo_maxu ||
                             arb_req.op.is_amo_min  ||
                             arb_req.op.is_amo_minu )) -> (arb_req.size inside {2,3})) else
                    $error("uc_handler: amo requests shall be 4 or 8 bytes wide");

    assert property (@(posedge clk_i) disable iff (!rst_ni)
            (mem_resp_write_valid_i || mem_resp_read_valid_i) -> (uc_fsm_q == UC_MEM_WAIT_RSP)) else
                    $error("uc_handler: unexpected response from memory");
`endif
//  }}}

endmodule

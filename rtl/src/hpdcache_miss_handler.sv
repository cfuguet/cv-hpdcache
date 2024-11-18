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
 *  Creation Date : April, 2021
 *  Description   : HPDcache Miss Handler
 *  History       :
 */
module hpdcache_miss_handler
//  {{{
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_word_t = logic,

    parameter type hpdcache_way_vector_t = logic,
    parameter type hpdcache_way_t = logic,

    parameter type hpdcache_refill_data_t = logic,

    parameter type hpdcache_mshr_id_t = logic,

    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_tid_t = logic,

    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,

    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_resp_r_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //      MISS interface
    //      {{{
    //          MISS request interface
    input  logic                  miss_req_valid_i [HPDcacheCfg.u.nBanks],
    output logic                  miss_req_ready_o [HPDcacheCfg.u.nBanks],
    input  hpdcache_nline_t       miss_req_nline_i [HPDcacheCfg.u.nBanks],
    input  hpdcache_req_tid_t     miss_req_tid_i   [HPDcacheCfg.u.nBanks],

    //          REFILL MISS / Invalidation interface
    input  logic                  refill_req_ready_i,
    output logic                  refill_req_valid_o,
    output logic                  refill_is_error_o,
    output logic                  refill_busy_o,
    output logic                  refill_write_dir_o,
    output logic                  refill_write_data_o,
    output hpdcache_refill_data_t refill_data_o,
    output hpdcache_word_t        refill_word_o,
    output logic                  refill_updt_rtab_o,

    output logic                  inval_check_dir_o,
    output logic                  inval_write_dir_o,
    output hpdcache_nline_t       inval_nline_o,
    input  logic                  inval_hit_i,
    //      }}}

    //      MSHR ACK interface
    //      {{{
    output logic                  mshr_ack_o    [HPDcacheCfg.u.nBanks],
    output logic                  mshr_ack_cs_o [HPDcacheCfg.u.nBanks],
    output hpdcache_mshr_id_t     mshr_ack_id_o [HPDcacheCfg.u.nBanks],
    //      }}}

    //      MEMORY interface
    //      {{{
    input  logic                  mem_req_ready_i,
    output logic                  mem_req_valid_o,
    output hpdcache_mem_req_t     mem_req_o,

    output logic                  mem_resp_ready_o,
    input  logic                  mem_resp_valid_i,
    input  hpdcache_mem_resp_r_t  mem_resp_i,
    input  logic                  mem_resp_inval_i,
    input  hpdcache_nline_t       mem_resp_inval_nline_i
    //      }}}
);
//  }}}

    //  Declaration of constants and types
    //  {{{
    localparam hpdcache_uint REFILL_REQ_RATIO = HPDcacheCfg.u.accessWords /
                                                HPDcacheCfg.u.reqWords;
    localparam hpdcache_uint REFILL_LAST_CHUNK_WORD = HPDcacheCfg.u.clWords -
                                                      HPDcacheCfg.u.accessWords;

    typedef enum logic {
        MISS_REQ_IDLE = 1'b0,
        MISS_REQ_SEND = 1'b1
    } miss_req_fsm_e;

    typedef enum {
        REFILL_IDLE,
        REFILL_WRITE,
        REFILL_WRITE_DIR,
        REFILL_INVAL
    } refill_fsm_e;

    typedef struct packed {
        hpdcache_mem_error_e r_error;
        hpdcache_mem_id_t    r_id;
        logic                is_inval;
        hpdcache_nline_t     inval_nline;
    } mem_resp_metadata_t;

    typedef struct packed {
        hpdcache_nline_t     nline;
        hpdcache_mem_id_t    tid;
    } core_miss_req_t;
    //  }}}

    //  Declaration of internal signals and registers
    //  {{{
    miss_req_fsm_e           miss_req_fsm_q, miss_req_fsm_d;

    refill_fsm_e             refill_fsm_q, refill_fsm_d;
    hpdcache_word_t          refill_cnt_q, refill_cnt_d;

    mem_resp_metadata_t      refill_fifo_resp_meta_wdata, refill_fifo_resp_meta_rdata;
    logic                    refill_fifo_resp_meta_w, refill_fifo_resp_meta_wok;
    logic                    refill_fifo_resp_meta_r, refill_fifo_resp_meta_rok;

    logic                    refill_fifo_resp_data_w, refill_fifo_resp_data_wok;
    hpdcache_refill_data_t   refill_fifo_resp_data_rdata;
    logic                    refill_fifo_resp_data_r;

    logic                    mshr_alloc;
    logic                    mshr_alloc_cs;

    core_miss_req_t          miss_req_w      [HPDcacheCfg.u.nBanks];
    core_miss_req_t [HPDcacheCfg.u.nBanks-1:0]         miss_fifo_rdata ;
    logic [HPDcacheCfg.u.nBanks-1:0] miss_fifo_rok   ;
    logic [HPDcacheCfg.u.nBanks-1:0] miss_fifo_r     ;
    logic                    miss_arb_ready;
    core_miss_req_t          miss_arb_req;
    hpdcache_nline_t         miss_send_nline_d, miss_send_nline_q;
    hpdcache_mem_id_t        miss_send_id_d, miss_send_id_q;
    logic [$clog2(HPDcacheCfg.u.nBanks)-1:0] miss_bank_id;

    logic [$clog2(HPDcacheCfg.u.nBanks)-1:0] refill_bank_id;
    //  }}}

    //  Miss Request FIFOs & MUX
    //  {{{
    generate
        genvar bank_i;

        for (bank_i = 0; bank_i < HPDcacheCfg.u.nBanks; bank_i++) begin: gen_miss_req_buf
            assign miss_req_w[bank_i].tid = miss_req_tid_i[bank_i],
                   miss_req_w[bank_i].nline = miss_req_nline_i[bank_i];

            hpdcache_fifo_reg #(
                .FIFO_DEPTH  (2),
                .FEEDTHROUGH (1),
                .fifo_data_t (core_miss_req_t)
            ) i_bank_miss_req_buf (
                .clk_i,
                .rst_ni,
                .w_i         (miss_req_valid_i[bank_i]),
                .wok_o       (miss_req_ready_o[bank_i]),
                .wdata_i     (miss_req_w[bank_i]),
                .r_i         (miss_fifo_r[bank_i] & miss_arb_ready),
                .rok_o       (miss_fifo_rok[bank_i]),
                .rdata_o     (miss_fifo_rdata[bank_i])
            );
        end
    endgenerate

    //      Arbiter
    hpdcache_fxarb #(.N(HPDcacheCfg.u.nBanks)) req_arbiter_i
    (
        .clk_i,
        .rst_ni,
        .req_i          (miss_fifo_rok),
        .gnt_o          (miss_fifo_r),
        .ready_i        (miss_arb_ready)
    );

    //      Request multiplexor
    hpdcache_mux #(
        .NINPUT         (HPDcacheCfg.u.nBanks),
        .DATA_WIDTH     ($bits(core_miss_req_t)),
        .ONE_HOT_SEL    (1'b1)
    ) core_req_mux_i (
        .data_i         (miss_fifo_rdata),
        .sel_i          (miss_fifo_r),
        .data_o         (miss_arb_req)
    );

    hpdcache_1hot_to_binary #(.N(HPDcacheCfg.u.nBanks)) id_gen_i (
        .val_i(miss_fifo_r),
        .val_o(miss_bank_id)
    );
    //  }}}

    //  Miss Request FSM
    //  {{{
    always_comb
    begin : miss_req_fsm_comb
        mem_req_valid_o    = 1'b0;
        miss_arb_ready     = 1'b0;

        miss_req_fsm_d     = miss_req_fsm_q;
        miss_send_nline_d  = miss_send_nline_q;
        miss_send_id_d     = miss_send_nline_q;

        unique case (miss_req_fsm_q)
            MISS_REQ_IDLE: begin
                miss_arb_ready = 1'b1;
                if (|miss_fifo_r) begin
                    miss_req_fsm_d = MISS_REQ_SEND;
                    miss_send_nline_d = miss_arb_req.nline;
                    miss_send_id_d = hpdcache_mem_id_t'({miss_bank_id, miss_arb_req.tid});
                end else begin
                    miss_req_fsm_d = MISS_REQ_IDLE;
                end
            end
            MISS_REQ_SEND: begin
                mem_req_valid_o = 1'b1;
                if (mem_req_ready_i) begin
                    miss_req_fsm_d = MISS_REQ_IDLE;
                end else begin
                    miss_req_fsm_d = MISS_REQ_SEND;
                end
            end
        endcase
    end

    localparam hpdcache_uint REFILL_REQ_SIZE = $clog2(HPDcacheCfg.u.memDataWidth / 8);
    localparam hpdcache_uint REFILL_REQ_LEN = HPDcacheCfg.clWidth / HPDcacheCfg.u.memDataWidth;

    assign mem_req_o.mem_req_addr = {miss_send_nline_q, {HPDcacheCfg.clOffsetWidth{1'b0}} };
    assign mem_req_o.mem_req_len = hpdcache_mem_len_t'(REFILL_REQ_LEN-1);
    assign mem_req_o.mem_req_size = hpdcache_mem_size_t'(REFILL_REQ_SIZE);
    assign mem_req_o.mem_req_command = HPDCACHE_MEM_READ;
    assign mem_req_o.mem_req_atomic = HPDCACHE_MEM_ATOMIC_ADD;
    assign mem_req_o.mem_req_cacheable = 1'b1;
    assign mem_req_o.mem_req_id = miss_send_id_q;

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : miss_req_fsm_ff
        if (!rst_ni) begin
            miss_req_fsm_q <= MISS_REQ_IDLE;
        end else begin
            miss_req_fsm_q <= miss_req_fsm_d;
            miss_send_nline_q <= miss_send_nline_d;
            miss_send_id_q <= miss_send_id_d;
        end
    end
    //  }}}

    //  Refill FSM
    //  {{{

    //      ask permission to the refill arbiter if there is a pending refill
    assign refill_req_valid_o  = refill_fsm_q == REFILL_IDLE ? refill_fifo_resp_meta_rok : 1'b0;

    if (HPDcacheCfg.u.nBanks > 1) begin
        assign refill_bank_id = refill_fifo_resp_meta_rdata.r_id[$bits(hpdcache_mem_id_t)-1 -: $clog2(HPDcacheCfg.u.nBanks)];
    end else begin
        assign refill_bank_id = 0;
    end

    always_comb
    begin : miss_resp_fsm_comb
        refill_write_dir_o      = 1'b0;
        refill_write_data_o     = 1'b0;
        refill_updt_rtab_o      = 1'b0;
        refill_cnt_d            = refill_cnt_q;

        inval_check_dir_o       = 1'b0;
        inval_write_dir_o       = 1'b0;

        refill_fifo_resp_meta_r = 1'b0;
        refill_fifo_resp_data_r = 1'b0;

        for (int unsigned i = 0; i < HPDcacheCfg.u.nBanks; i++) begin
            mshr_ack_cs_o[i] = 1'b0;
            mshr_ack_o[i]    = 1'b0;
            mshr_ack_id_o[i] = '0;
        end

        refill_fsm_d            = refill_fsm_q;

        case (refill_fsm_q)
            //  Wait for refill responses
            //  {{{
            REFILL_IDLE: begin
                if (refill_fifo_resp_meta_rok) begin
                    //  anticipate the activation of the MSHR independently of the grant signal from
                    //  the refill arbiter. This is to avoid the introduction of unnecessary timing
                    //  paths (however there could be a minor augmentation of the power consumption)
                    mshr_ack_cs_o[refill_bank_id] = ~refill_fifo_resp_meta_rdata.is_inval;

                    //  if the permission is granted, start refilling
                    if (refill_req_ready_i) begin

                        if (refill_fifo_resp_meta_rdata.is_inval) begin
                            //  check for a match with the line being invalidated in the cache dir
                            inval_check_dir_o = 1'b1;

                            refill_fsm_d = REFILL_INVAL;
                        end else begin
                            //  read the MSHR and reset the valid bit for the corresponding entry
                            mshr_ack_o[refill_bank_id] = ~refill_fifo_resp_meta_rdata.is_inval;
                            mshr_ack_id_o[refill_bank_id] = refill_fifo_resp_meta_rdata.r_id[HPDcacheCfg.mshrIdWidth-1:0];

                            //  initialize the counter for refill words
                            refill_cnt_d = 0;
                            refill_fsm_d = REFILL_WRITE;
                        end
                    end
                end
            end
            //  }}}

            //  Write refill data into the cache
            //  {{{
            REFILL_WRITE: begin

                //  Write the the data in the cache data array
                refill_write_data_o = ~refill_is_error_o;

                //  Consume chunk of data from the FIFO buffer in the memory interface
                refill_fifo_resp_data_r = 1'b1;

                //  Update directory on the last chunk of data
                refill_cnt_d = refill_cnt_q + hpdcache_word_t'(HPDcacheCfg.u.accessWords);

                if (hpdcache_uint'(refill_cnt_q) == REFILL_LAST_CHUNK_WORD) begin
                    if (REFILL_LAST_CHUNK_WORD == 0) begin
                        //  Special case: if the cache-line data can be written in a single cycle,
                        //  wait an additional cycle to write the directory. This allows to prevent
                        //  a RAM-to-RAM timing path between the MSHR and the DIR.
                        refill_fsm_d = REFILL_WRITE_DIR;
                    end else begin
                        //  Write the new entry in the cache directory
                        refill_write_dir_o = 1'b1;

                        //  Update dependency flags in the retry table
                        refill_updt_rtab_o  = 1'b1;

                        //  consume the response from the network
                        refill_fifo_resp_meta_r = 1'b1;

                        refill_fsm_d = REFILL_IDLE;
                    end
                end
            end
            //  }}}

            //  Write cache directory (this state is only visited when ACCESS_WORDS == CL_WORDS,
            //  this is when the entire cache-line can be written in a single cycle)
            //  {{{
            REFILL_WRITE_DIR: begin
                //  Write the new entry in the cache directory
                refill_write_dir_o  = 1'b1;

                //  Update dependency flags in the retry table
                refill_updt_rtab_o = 1'b1;

                //  consume the response from the network
                refill_fifo_resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end
            //  }}}

            //  Invalidate the target cacheline (if it matches a valid cacheline)
            //  {{{
            REFILL_INVAL: begin
                //  Invalidate if there is a match
                inval_write_dir_o = inval_hit_i;

                //  consume the invalidation from the network
                refill_fifo_resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end

            default: begin
`ifndef HPDCACHE_ASSERT_OFF
                assert (1) $error("miss_handler: illegal state");
`endif
            end
        endcase
    end

    assign refill_is_error_o = (refill_fifo_resp_meta_rdata.r_error == HPDCACHE_MEM_RESP_NOK);

    assign refill_busy_o  = (refill_fsm_q != REFILL_IDLE);
    assign refill_word_o  = refill_cnt_q;

    assign inval_nline_o = refill_fifo_resp_meta_rdata.inval_nline;

    /* FIXME: when multiple chunks, in case of error, the error bit is not
     *        necessarily set on all chunks */
    assign refill_fifo_resp_meta_wdata = '{
        r_error    : mem_resp_i.mem_resp_r_error,
        r_id       : mem_resp_i.mem_resp_r_id,
        is_inval   : mem_resp_inval_i,
        inval_nline: mem_resp_inval_nline_i
    };

    hpdcache_fifo_reg #(
        .FIFO_DEPTH  (HPDcacheCfg.u.refillFifoDepth),
        .fifo_data_t (mem_resp_metadata_t)
    ) i_r_metadata_fifo (
        .clk_i,
        .rst_ni,

        .w_i    (refill_fifo_resp_meta_w),
        .wok_o  (refill_fifo_resp_meta_wok),
        .wdata_i(refill_fifo_resp_meta_wdata),

        .r_i    (refill_fifo_resp_meta_r),
        .rok_o  (refill_fifo_resp_meta_rok),
        .rdata_o(refill_fifo_resp_meta_rdata)
    );

    hpdcache_data_resize #(
        .WR_WIDTH (HPDcacheCfg.u.memDataWidth),
        .RD_WIDTH (HPDcacheCfg.accessWidth),
        .DEPTH    (HPDcacheCfg.u.refillFifoDepth)
    ) i_data_resize(
        .clk_i,
        .rst_ni,

        .w_i    (refill_fifo_resp_data_w),
        .wok_o  (refill_fifo_resp_data_wok),
        .wdata_i(mem_resp_i.mem_resp_r_data),
        .wlast_i(mem_resp_i.mem_resp_r_last),

        .r_i    (refill_fifo_resp_data_r),
        .rok_o  (/* unused */),
        .rdata_o(refill_fifo_resp_data_rdata),
        .rlast_o(/* unused */)
    );

    assign refill_data_o = refill_fifo_resp_data_rdata;

    //      The DATA fifo is only used for refill responses
    assign refill_fifo_resp_data_w = mem_resp_valid_i &
            ((refill_fifo_resp_meta_wok | ~mem_resp_i.mem_resp_r_last) &
            ~mem_resp_inval_i);

    //      The METADATA fifo is used for both refill responses and invalidations
    assign refill_fifo_resp_meta_w = mem_resp_valid_i &
            ((refill_fifo_resp_data_wok & mem_resp_i.mem_resp_r_last) |
            mem_resp_inval_i);

    always_comb
    begin : mem_resp_ready_comb
        mem_resp_ready_o = 1'b0;
        if (mem_resp_valid_i) begin
            if (mem_resp_inval_i) begin
                mem_resp_ready_o = refill_fifo_resp_meta_wok;
            end else begin
                mem_resp_ready_o = (refill_fifo_resp_meta_wok | ~mem_resp_i.mem_resp_r_last) &
                                    refill_fifo_resp_data_wok;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : miss_resp_fsm_ff
        if (!rst_ni) begin
            refill_fsm_q <= REFILL_IDLE;
        end else begin
            refill_fsm_q <= refill_fsm_d;
        end
    end

    always_ff @(posedge clk_i)
    begin : miss_resp_fsm_internal_ff
        refill_cnt_q <= refill_cnt_d;
    end
    //  }}}
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
`endif
    //  }}}

endmodule
//  }}}

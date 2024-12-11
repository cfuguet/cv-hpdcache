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
    parameter type hpdcache_mem_resp_r_t = logic,

    localparam int unsigned nBanks = HPDcacheCfg.u.nBanks
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
    input  logic                  miss_req_valid_i    [nBanks],
    output logic                  miss_req_ready_o    [nBanks],
    input  hpdcache_nline_t       miss_req_nline_i    [nBanks],
    input  hpdcache_mshr_id_t     miss_req_mshr_id_i  [nBanks],

    //          REFILL MISS / Invalidation interface
    input  logic                  refill_req_ready_i  [nBanks],
    output logic                  refill_req_valid_o  [nBanks],
    output logic                  refill_is_error_o,
    output logic [nBanks-1:0]     refill_busy_o,
    output logic                  refill_write_dir_o  [nBanks],
    output logic                  refill_write_data_o [nBanks],
    output hpdcache_refill_data_t refill_data_o,
    output hpdcache_word_t        refill_word_o,
    output logic                  refill_updt_rtab_o  [nBanks],

    output logic                  inval_check_dir_o   [nBanks],
    output logic                  inval_write_dir_o   [nBanks],
    output hpdcache_nline_t       inval_nline_o,
    input  logic                  inval_hit_i         [nBanks],
    //      }}}

    //      MSHR ACK interface
    //      {{{
    output logic                  mshr_ack_o    [nBanks],
    output logic                  mshr_ack_cs_o [nBanks],
    output hpdcache_mshr_id_t     mshr_ack_id_o [nBanks],
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
    localparam hpdcache_uint REFILL_LAST_CHUNK_WORD = HPDcacheCfg.u.clWords -
                                                      HPDcacheCfg.u.accessWords;
    localparam hpdcache_uint BANK_ID_WIDTH = nBanks > 1 ? $clog2(nBanks) : 1;

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
        hpdcache_mshr_id_t   mshr_id;
    } mem_miss_req_t;
    //  }}}

    //  Declaration of internal signals and registers
    //  {{{
    miss_req_fsm_e           miss_req_fsm_q, miss_req_fsm_d;

    refill_fsm_e             refill_fsm_q, refill_fsm_d;
    hpdcache_word_t          refill_cnt_q, refill_cnt_d;

    mem_resp_metadata_t      resp_meta_wdata, resp_meta_rdata;
    logic                    resp_meta_w, resp_meta_wok;
    logic                    resp_meta_r, resp_meta_rok;

    logic                    resp_data_w, resp_data_wok;
    hpdcache_refill_data_t   resp_data_rdata;
    logic                    resp_data_r;

    mem_miss_req_t [nBanks-1:0] miss_fifo_rdata;
    logic [nBanks-1:0]          miss_fifo_rok;
    logic [nBanks-1:0]          miss_fifo_r;

    mem_miss_req_t            miss_req_w [nBanks];
    logic                     miss_arb_ready;
    mem_miss_req_t            miss_arb_req;
    hpdcache_nline_t          miss_send_nline_d, miss_send_nline_q;
    hpdcache_mem_id_t         miss_send_id_d, miss_send_id_q;
    logic [BANK_ID_WIDTH-1:0] miss_bank_id;

    logic [BANK_ID_WIDTH-1:0]        refill_bank_id;
    logic [nBanks-1:0] refill_req_valid /*verilator isolate_assignments*/;

    genvar bank_i;
    //  }}}

    //  Miss Request FIFOs & MUX
    //  {{{

    for (bank_i = 0; bank_i < nBanks; bank_i++) begin: gen_miss_req_buf
        assign miss_req_w[bank_i].mshr_id = miss_req_mshr_id_i[bank_i];
        assign miss_req_w[bank_i].nline = miss_req_nline_i[bank_i];

        hpdcache_fifo_reg #(
            .FIFO_DEPTH  (2),
            .FEEDTHROUGH (1),
            .fifo_data_t (mem_miss_req_t)
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

    //      Arbiter
    hpdcache_fxarb #(.N(nBanks)) req_arbiter_i
    (
        .clk_i,
        .rst_ni,
        .req_i          (miss_fifo_rok),
        .gnt_o          (miss_fifo_r),
        .ready_i        (miss_arb_ready)
    );

    //      Request multiplexor
    hpdcache_mux #(
        .NINPUT         (nBanks),
        .DATA_WIDTH     ($bits(mem_miss_req_t)),
        .ONE_HOT_SEL    (1'b1)
    ) core_req_mux_i (
        .data_i         (miss_fifo_rdata),
        .sel_i          (miss_fifo_r),
        .data_o         (miss_arb_req)
    );

    hpdcache_1hot_to_binary #(.N(nBanks)) id_gen_i (
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
        miss_send_id_d     = miss_send_id_q;

        unique case (miss_req_fsm_q)
            MISS_REQ_IDLE: begin
                miss_arb_ready = 1'b1;
                if (|miss_fifo_r) begin
                    miss_req_fsm_d = MISS_REQ_SEND;
                    miss_send_nline_d = miss_arb_req.nline;
                    miss_send_id_d = hpdcache_mem_id_t'({miss_bank_id, miss_arb_req.mshr_id});
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
        end
    end

    always_ff @(posedge clk_i)
    begin
        miss_send_nline_q <= miss_send_nline_d;
        miss_send_id_q    <= miss_send_id_d;
    end
    //  }}}

    //  Refill FSM
    //  {{{
    //      ask permission to the refill arbiter if there is a pending refill
    if (nBanks > 1) begin : gen_refill_bank_id_nbanks_gt_1
        assign refill_bank_id = resp_meta_rdata.r_id[HPDcacheCfg.mshrIdWidth +: BANK_ID_WIDTH];
    end else begin : gen_refill_bank_id_nbanks_not_gt_1
        assign refill_bank_id = 0;
    end

    for (bank_i = 0; bank_i < nBanks; bank_i++) begin : gen_refill_valid
        assign refill_req_valid_o[bank_i] = refill_req_valid[bank_i];
    end

    always_comb
    begin : miss_resp_fsm_comb
        refill_req_valid    = '{default:1'b0};
        refill_write_dir_o  = '{default:1'b0};
        refill_write_data_o = '{default:1'b0};
        refill_updt_rtab_o  = '{default:1'b0};
        refill_cnt_d        = refill_cnt_q;
        refill_fsm_d        = refill_fsm_q;

        resp_meta_r = 1'b0;
        resp_data_r = 1'b0;

        inval_check_dir_o   = '{default:1'b0};
        inval_write_dir_o   = '{default:1'b0};

        mshr_ack_cs_o = '{default:1'b0};
        mshr_ack_o    = '{default:1'b0};
        mshr_ack_id_o = '{default:'0};

        case (refill_fsm_q)
            //  Wait for refill responses
            //  {{{
            REFILL_IDLE: begin
                if (resp_meta_rok) begin
                    //  FIXME in case of invalidation, the bank ID shall be
                    //  decoded from the invalidation nline (applying the same
                    //  mapping as for the requests)
                    refill_req_valid[refill_bank_id] = 1'b1;

                    //  anticipate the activation of the MSHR independently of the grant signal from
                    //  the refill arbiter. This is to avoid the introduction of unnecessary timing
                    //  paths (however there could be a minor augmentation of the power consumption)
                    mshr_ack_cs_o[refill_bank_id] = ~resp_meta_rdata.is_inval;

                    //  if the permission is granted, start refilling
                    if (refill_req_ready_i[refill_bank_id]) begin
                        if (resp_meta_rdata.is_inval) begin
                            //  check for a match with the line being invalidated in the cache dir
                            // inval_check_dir_o = 1'b1; //FIXME

                            refill_fsm_d = REFILL_INVAL;
                        end else begin
                            //  read the MSHR and reset the valid bit for the corresponding entry
                            mshr_ack_o[refill_bank_id] = ~resp_meta_rdata.is_inval;
                            mshr_ack_id_o[refill_bank_id] = resp_meta_rdata.r_id[HPDcacheCfg.mshrIdWidth-1:0];

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
                refill_write_data_o[refill_bank_id] = ~refill_is_error_o;

                //  Consume chunk of data from the FIFO buffer in the memory interface
                resp_data_r = 1'b1;

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
                        refill_write_dir_o[refill_bank_id] = 1'b1;

                        //  Update dependency flags in the retry table
                        refill_updt_rtab_o[refill_bank_id] = 1'b1;

                        //  consume the response from the network
                        resp_meta_r = 1'b1;

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
                refill_write_dir_o[refill_bank_id] = 1'b1;

                //  Update dependency flags in the retry table
                refill_updt_rtab_o[refill_bank_id] = 1'b1;

                //  consume the response from the network
                resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end
            //  }}}

            //  Invalidate the target cacheline (if it matches a valid cacheline)
            //  {{{
            REFILL_INVAL: begin
                //  Invalidate if there is a match
                // inval_write_dir_o = inval_hit_i;//FIXME

                //  consume the invalidation from the network
                resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end

            default: begin
`ifndef HPDCACHE_ASSERT_OFF
                assert (1) $error("miss_handler: illegal state");
`endif
            end
        endcase
    end

    assign refill_is_error_o = (resp_meta_rdata.r_error == HPDCACHE_MEM_RESP_NOK);

    always_comb begin : refill_busy_comb
        for (int unsigned bank = 0; bank < nBanks; bank++) begin
            refill_busy_o[bank] = bank == refill_bank_id && (refill_fsm_q != REFILL_IDLE);
        end
    end

    assign refill_word_o  = refill_cnt_q;

    assign inval_nline_o = resp_meta_rdata.inval_nline;

    /* FIXME: when multiple chunks, in case of error, the error bit is not
     *        necessarily set on all chunks */
    assign resp_meta_wdata = '{
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

        .w_i    (resp_meta_w),
        .wok_o  (resp_meta_wok),
        .wdata_i(resp_meta_wdata),

        .r_i    (resp_meta_r),
        .rok_o  (resp_meta_rok),
        .rdata_o(resp_meta_rdata)
    );

    hpdcache_data_resize #(
        .WR_WIDTH (HPDcacheCfg.u.memDataWidth),
        .RD_WIDTH (HPDcacheCfg.accessWidth),
        .DEPTH    (HPDcacheCfg.u.refillFifoDepth)
    ) i_data_resize(
        .clk_i,
        .rst_ni,

        .w_i    (resp_data_w),
        .wok_o  (resp_data_wok),
        .wdata_i(mem_resp_i.mem_resp_r_data),
        .wlast_i(mem_resp_i.mem_resp_r_last),

        .r_i    (resp_data_r),
        .rok_o  (/* unused */),
        .rdata_o(resp_data_rdata),
        .rlast_o(/* unused */)
    );

    assign refill_data_o = resp_data_rdata;

    //      The DATA fifo is only used for refill responses
    assign resp_data_w = mem_resp_valid_i &
            ((resp_meta_wok | ~mem_resp_i.mem_resp_r_last) &
            ~mem_resp_inval_i);

    //      The METADATA fifo is used for both refill responses and invalidations
    assign resp_meta_w = mem_resp_valid_i &
            ((resp_data_wok & mem_resp_i.mem_resp_r_last) |
            mem_resp_inval_i);

    always_comb
    begin : mem_resp_ready_comb
        mem_resp_ready_o = 1'b0;
        if (mem_resp_valid_i) begin
            if (mem_resp_inval_i) begin
                mem_resp_ready_o = resp_meta_wok;
            end else begin
                mem_resp_ready_o = (resp_meta_wok | ~mem_resp_i.mem_resp_r_last) & resp_data_wok;
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

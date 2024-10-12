`include "./include/AXI_define.svh"
module axi4pc_sva(
    input                           ACLK,
    input                           ARESETn,

    input   [`AXI_ADDR_BITS-1:0 ]   AWADDR,   
    input   [`AXI_LEN_BITS-1:0  ]   AWLEN,
    input   [`AXI_SIZE_BITS-1:0 ]   AWSIZE,
    input                           AWVALID,
    input   [1:0                ]   AWBURST,
    input                           AWREADY,
    input   [`AXI_ID_BITS-1:0   ]   AWID,

    input                           WVALID,
    input                           WREADY,
    input                           WLAST,
    input	[`AXI_STRB_BITS-1:0 ]   WSTRB,
    input   [`AXI_DATA_BITS-1:0 ]   WDATA,

    input                           BVALID,
    input                           BREADY,
    input	[`AXI_ID_BITS-1:0	]	BID,
    input   [1:0                ]   BRESP,

    input   [`AXI_ADDR_BITS-1:0	]   ARADDR,
    input                           ARVALID,
    input                           ARREADY,
    input   [`AXI_LEN_BITS-1:0	]   ARLEN,
    input   [`AXI_SIZE_BITS-1:0 ]   ARSIZE,
    input   [1:0                ]   ARBURST,
    input   [`AXI_ID_BITS-1:0   ]   ARID,

    input                           RVALID,
    input                           RREADY,
    input                           RLAST,
    input   [`AXI_DATA_BITS-1:0 ]   RDATA,
    input   [`AXI_IDS_BITS-1:0  ]   RID,
    input   [1:0                ]   RRESP

);

    // ******************************************************
    // WRITE ADDRESS CHANNEL
    // ******************************************************

    AXI_ERRM_AWBURST: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> (AWBURST != 2'b11)
        )
    );

    AXI_ERRM_AWSIZE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ('d1 << AWSIZE) * 8 <= `AXI_ADDR_BITS
        )
    );

    AXI_ERRM_AWVALID_RESET: assert property(
        @(posedge ACLK)(
            ~ARESETn ##1 ARESETn |-> ~AWVALID
        )
    );

    AXI_ERRM_AWADDR_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWADDR)
        )
    );

    AXI_ERRM_AWBURST_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWBURST)
        )
    );

    AXI_ERRM_AWID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWID)
        )
    );

    AXI_ERRM_AWLEN_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWLEN)
        )
    );

    AXI_ERRM_AWSIZE_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWSIZE)
        )
    );

    AXI_ERRM_AWVALID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (AWVALID & ~AWREADY) |-> ##1 $stable(AWVALID)
        )
    );


    // ******************************************************
    // WRITE DATA CHANNEL
    // ******************************************************

    logic [31:0] beat_cnt;

    always_ff @(posedge ACLK, negedge ARESETn) begin
        if (~ARESETn) begin
            beat_cnt <= 'd0;
        end else if (AWVALID && AWREADY) begin
            beat_cnt <= AWLEN + 'd1;
        end else if (WVALID && WREADY) begin
            beat_cnt <= beat_cnt - 'd1;
        end else begin
            beat_cnt <= beat_cnt;
        end
    end


    // Write data arrives, WLAST is set, and the WDATA count is not equal to AWLEN
    AXI_ERRM_WDATA_NUM_1: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WLAST |-> (beat_cnt == 'd1)
        )
    );

    // Write data arrives, WLAST is not set, and the WDATA count is equal to AWLEN
    AXI_ERRM_WDATA_NUM_2: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (WVALID && WREADY) && (beat_cnt == 'd1) |-> WLAST
        )
    );

    // ADDR arrives, WLAST is already received, and the WDATA count is not equal to AWLEN
    AXI_ERRM_WDATA_NUM_3: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> (beat_cnt == 'd0)
        )
    );

    AXI_ERRM_WVALID_RESET: assert property(
        @(posedge ACLK)(
            ~ARESETn ##1 ARESETn |-> ~AWVALID
        )
    );

    AXI_ERRM_WDATA_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID && ~WREADY |-> ##1 $stable(WDATA)
        )
    );

    AXI_ERRM_WLAST_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID && ~WREADY |-> ##1 $stable(WDATA)
        )
    );

    AXI_ERRM_WSTRB_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID && ~WREADY |-> ##1 $stable(WSTRB)
        )
    );

    AXI_ERRM_WVALID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID && ~WREADY |-> ##1 $stable(WVALID)
        )
    );

    // ******************************************************
    // WRITE RESPONSE CHANNEL
    // ******************************************************

    AXI_ERRS_BVALID_RESET: assert property(
        @(posedge ACLK)(
            ~ARESETn ##1 ARESETn |-> ~BVALID
        )
    );

    logic wlast_seen;
    always_ff @(posedge ACLK, negedge ARESETn) begin
        if (~ARESETn) begin
            wlast_seen <= 'd0;
        end else if (WLAST) begin
            wlast_seen <= 'd1;
        end else if (BVALID && BREADY) begin
            wlast_seen <= 'd0;
        end else begin
            wlast_seen <= wlast_seen;
        end
    end

    AXI_ERRS_BRESP_WLAST: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID |-> (wlast_seen == 'd1)
        )
    );

    AXI_ERRS_BID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID && ~BREADY |-> ##1 $stable(BID)
        )
    );

    AXI_ERRS_BRESP_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID && ~BREADY |-> ##1 $stable(BRESP)
        )
    );

    AXI_ERRS_BVALID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID && ~BREADY |-> ##1 $stable(BVALID)
        )
    );


    // ******************************************************
    // READ ADDRESS CHANNEL
    // ******************************************************

    AXI_ERRM_ARBURST: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> (ARBURST != 2'b11)
        )
    );

    AXI_ERRM_ARSIZE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
           ('d1 << ARSIZE) * 8 <= `AXI_ADDR_BITS
        )
    );

    AXI_ERRM_ARVALID_RESET: assert property(
        @(posedge ACLK)(
            ~ARESETn ##1 ARESETn |-> ~ARVALID
        )
    );

    AXI_ERRM_ARADDR_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARADDR)
        )
    );

    AXI_ERRM_ARBURST_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARBURST)
        )
    );

    AXI_ERRM_ARID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARID)
        )
    );

    AXI_ERRM_ARLEN_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARLEN)
        )
    );

    AXI_ERRM_ARSIZE_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARSIZE)
        )
    );

    AXI_ERRM_ARVALID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID && ~ARREADY |-> ##1 $stable(ARVALID)
        )
    );
    // ******************************************************
    // READ DATA CHANNEL
    // ******************************************************

    logic [31:0] read_cnt;

    always_ff @(posedge ACLK, negedge ARESETn) begin
        if (~ARESETn) begin
            read_cnt <= 'd0;
        end else if (ARVALID && ARREADY) begin
            read_cnt <= ARLEN + 'd1;
        end else if (RVALID && RREADY) begin
            read_cnt <= read_cnt -'d1;
        end else begin
            read_cnt <= read_cnt;
        end
    end

    AXI_ERRS_RDATA_NUM_1: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (RLAST |-> (read_cnt == 'd1))
        )
    );

    AXI_ERRS_RDATA_NUM_2: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            (read_cnt != 'd1) |-> ~RLAST
        )
    );

    AXI_ERRS_RVALID_RESET: assert property(
        @(posedge ACLK)(
            ~ARESETn ##1 ARESETn |-> ~RVALID
        )
    );

    AXI_ERRS_RDATA_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID && ~RREADY |-> ##1 $stable(RDATA)
        )
    );

    AXI_ERRS_RID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID && ~RREADY |-> ##1 $stable(RID)
        )
    );

    AXI_ERRS_RLAST_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID && ~RREADY |-> ##1 $stable(RLAST)
        )
    );

    AXI_ERRS_RRESP_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID && ~RREADY |-> ##1 $stable(RRESP)
        )
    );

    AXI_ERRS_RVALID_STABLE: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID && ~RREADY |-> ##1 $stable(RVALID)
        )
    );

    // *********************

    AXI_ERRM_ARADDR_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> ~$isunknown(ARADDR)            
        )
    );

    AXI_ERRM_ARBURST_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> ~$isunknown(ARBURST)
        )
    );

    AXI_ERRM_ARID_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> ~$isunknown(ARID)
        )
    );

    AXI_ERRM_ARLEN_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> ~$isunknown(ARLEN)
        )
    );

    AXI_ERRM_ARSIZE_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            ARVALID |-> ~$isunknown(ARSIZE)
        )
    );

    AXI_ERRM_ARVALID_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(ARVALID)
        )
    );

    AXI_ERRM_AWADDR_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> ~$isunknown(AWADDR)
        )
    );

    AXI_ERRM_AWBURST_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> ~$isunknown(AWBURST)
        )
    );

    AXI_ERRM_AWID_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> ~$isunknown(AWID)
        )
    );

    AXI_ERRM_AWLEN_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> ~$isunknown(AWLEN)
        )
    );

    AXI_ERRM_AWSIZE_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            AWVALID |-> ~$isunknown(AWSIZE)
        )
    );

    AXI_ERRM_AWVALID_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(AWVALID)
        )
    );

    AXI_ERRM_BREADY_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(BREADY)
        )
    );

    AXI_ERRM_RREADY_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(RREADY)
        )
    );

    AXI_ERRM_WDATA_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID |-> ~$isunknown(WDATA)
        )
    );

    AXI_ERRM_WLAST_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID |-> ~$isunknown(WLAST)
        )
    );

    AXI_ERRM_WSTRB_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            WVALID |-> ~$isunknown(WSTRB)
        )
    );

    AXI_ERRM_WVALID_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(WVALID)
        )
    );

    AXI_ERRS_ARREADY_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(ARREADY)
        )
    );

    AXI_ERRS_AWREADY_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(AWREADY)
        )
    );

    AXI_ERRS_BID_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID |-> ~$isunknown(BID)
        )
    );

    AXI_ERRS_BRESP_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            BVALID |-> ~$isunknown(BRESP)
        )
    );

    AXI_ERRS_BVALID_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(BVALID)
        )
    );

    AXI_ERRS_RDATA_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID |-> ~$isunknown(RDATA)
        )
    );

    AXI_ERRS_RID_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID |-> ~$isunknown(RID)
        )
    );

    AXI_ERRS_RLAST_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID |-> ~$isunknown(RLAST)
        )
    );

    AXI_ERRS_RRESP_X: assert property(
        @(posedge ACLK) disable iff (~ARESETn)(
            RVALID |-> ~$isunknown(RRESP)
        )
    );

    AXI_ERRS_RVALID_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(RVALID)
        )
    );

    AXI_ERRS_WREADY_X: assert property(
        @(posedge ACLK)(
            ARESETn |-> ~$isunknown(WREADY)
        )
    );

endmodule

bind top axi4pc_sva axi4pc(
    .ACLK       (top.clk        ),
    .ARESETn    (AXI.ARESETn    ),

    .AWADDR     (AXI.AWADDR_M1  ),
    .AWSIZE     (AXI.AWSIZE_M1  ),
    .AWLEN      (AXI.AWLEN_M1   ),
    .AWVALID    (AXI.AWVALID_M1 ),
    .AWBURST    (AXI.AWBURST_M1 ),
    .AWREADY    (AXI.AWREADY_M1 ),
    .AWID       (AXI.AWID_M1    ),

    .WVALID     (AXI.WVALID_M1  ),
    .WREADY     (AXI.WREADY_M1  ),
    .WLAST      (AXI.WLAST_M1   ),
    .WSTRB      (AXI.WSTRB_M1   ),
    .WDATA      (AXI.WDATA_M1   ),

    .BVALID     (AXI.BVALID_S1  ),
    .BREADY     (AXI.BREADY_S1  ),
    .BID        (AXI.BID_S1     ),
    .BRESP      (AXI.BRESP_S1   ),

    .ARADDR     (AXI.ARADDR_M1  ),
    .ARVALID    (AXI.ARVALID_M1 ),
    .ARREADY    (AXI.ARREADY_M1 ),
    .ARLEN      (AXI.ARLEN_M1   ),
    .ARSIZE     (AXI.ARSIZE_M1  ),
    .ARBURST    (AXI.ARBURST_M1 ),
    .ARID       (AXI.ARID_M1    ),

    .RVALID     (AXI.RVALID_S1  ),
    .RREADY     (AXI.RREADY_M1  ),
    .RLAST      (AXI.RLAST_S1   ),
    .RDATA      (AXI.RDATA_S1   ),
    .RID        (AXI.RID_S1     ),
    .RRESP      (AXI.RRESP_S1   )

);

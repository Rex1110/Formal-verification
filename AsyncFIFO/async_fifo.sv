module async_fifo #(
    parameter FIFO_DEPTH = 8,
    parameter DATA_WIDTH = 8,
    parameter PTR_WIDTH  = $clog2(FIFO_DEPTH)
)(
    input                                   wr_clk,
    input                                   rd_clk,

    input                                   wr_rst_n,
    input                                   rd_rst_n,

    input                                   wr_en,
    input                                   rd_en,

    input           [DATA_WIDTH - 1: 0]     wr_data,
    
    output  logic   [DATA_WIDTH - 1: 0]     rd_data,
    output  logic                           full,
    output  logic                           empty
);
    logic [DATA_WIDTH - 1:0] fifo [FIFO_DEPTH - 1:0];
    logic [PTR_WIDTH:0] wr_ptr, rd_ptr;
    logic [PTR_WIDTH:0] wr_ptr_gray, rd_ptr_gray;
    logic [PTR_WIDTH:0] wr_ptr_gray_d1, rd_ptr_gray_d1;
    logic [PTR_WIDTH:0] wr_ptr_gray_d2, rd_ptr_gray_d2;

    always_ff @(posedge wr_clk, negedge wr_rst_n) begin
        if (~wr_rst_n) begin
            wr_ptr <= 'd0;
        end else begin
            if (wr_en && ~full) begin
                wr_ptr <= wr_ptr + 'd1;
            end else begin
                wr_ptr <= wr_ptr;
            end
        end
    end

    always_ff @(posedge rd_clk, negedge rd_rst_n) begin
        if (~rd_rst_n) begin
            rd_ptr <= 'd0;
        end else begin
            if (rd_en && ~empty) begin
                rd_ptr <= rd_ptr + 'd1;
            end else begin
                rd_ptr <= rd_ptr;
            end
        end
    end

    always_ff @(posedge wr_clk, negedge wr_rst_n) begin
        if (~wr_rst_n) begin
            fifo[wr_ptr[PTR_WIDTH - 1: 0]] <= 'd0;
        end else if (wr_en && ~full) begin
            fifo[wr_ptr[PTR_WIDTH - 1: 0]] <= wr_data;
        end else begin
        end
    end
    
    assign rd_data = fifo[rd_ptr[PTR_WIDTH - 1: 0]];

    assign wr_ptr_gray = (wr_ptr >> 1) ^ wr_ptr;
    assign rd_ptr_gray = (rd_ptr >> 1) ^ rd_ptr;

    always_ff @(posedge wr_clk, negedge wr_rst_n) begin
        if (~wr_rst_n) begin
            rd_ptr_gray_d1 <= 'd0;
            rd_ptr_gray_d2 <= 'd0;
        end else begin  
            rd_ptr_gray_d1 <= rd_ptr_gray;
            rd_ptr_gray_d2 <= rd_ptr_gray_d1;
        end
    end

    always_ff @(posedge rd_clk, negedge rd_rst_n) begin
        if (~rd_rst_n) begin
            wr_ptr_gray_d1 <= 'd0;
            wr_ptr_gray_d2 <= 'd0;
        end else begin
            wr_ptr_gray_d1 <= wr_ptr_gray;
            wr_ptr_gray_d2 <= wr_ptr_gray_d1;
        end
    end

    assign empty = (rd_ptr_gray == wr_ptr_gray_d2);
    assign full  = wr_ptr_gray == {~rd_ptr_gray_d2[PTR_WIDTH: PTR_WIDTH - 1], rd_ptr_gray_d2[PTR_WIDTH - 2: 0]};

    
endmodule
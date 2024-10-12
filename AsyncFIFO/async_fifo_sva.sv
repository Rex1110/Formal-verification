module async_fifo_sva #(
    parameter FIFO_DEPTH = 9, // 比 DUV 多1 !
    parameter DATA_WIDTH = 8,
    parameter PTR_WIDTH  = $clog2(FIFO_DEPTH)
)(
    input                                   wr_clk,
    input                                   rd_clk,

    input                                   wr_rst_n,
    input                                   rd_rst_n,

    input                                   wr_en,
    input                                   rd_en,

    input            [DATA_WIDTH - 1: 0]    wr_data,
    
    input   logic    [DATA_WIDTH - 1: 0]    rd_data,
    input   logic                           full,
    input   logic                           empty
);

    logic [DATA_WIDTH-1:0] queue [FIFO_DEPTH];
    logic [FIFO_DEPTH>>1:0] wr_ptr_q, rd_ptr_q;

    always_ff @(posedge wr_clk, negedge wr_rst_n) begin
        if (~wr_rst_n) begin
            wr_ptr_q <= 'd0;
        end else if (wr_en && ~full) begin
            queue[wr_ptr_q] <= wr_data;
            if (wr_ptr_q == FIFO_DEPTH-1) begin
                wr_ptr_q <= 'd0;
            end else begin
                wr_ptr_q <= wr_ptr_q + 'd1;
            end
        end else begin
            queue <= queue;
            wr_ptr_q <= wr_ptr_q;
        end
    end

    always_ff @(posedge rd_clk, negedge rd_rst_n) begin
        if (~rd_rst_n) begin
            rd_ptr_q <= 'd0;
        end else if (rd_en && ~empty) begin
            if (rd_ptr_q == FIFO_DEPTH-1) begin
                rd_ptr_q <= 'd0;
            end else begin
                rd_ptr_q <= rd_ptr_q + 'd1;
            end
        end
    end


    full_empty: assert property (
        ~(full && empty)
    );

    data_integrity: assert property (
        (rd_en && ~empty) |-> (queue[rd_ptr_q] == rd_data)
    );

    size1: cover property (
        (wr_ptr_q - rd_ptr_q) == 8
    );

    size2: cover property (
        (rd_ptr_q - wr_ptr_q) == -1
    );


endmodule

bind async_fifo async_fifo_sva top (
    .*
);
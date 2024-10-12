clear -all
check_cov -init -type all 

# file
analyze -sv "./async_fifo.sv"
analyze -sv "./async_fifo_sva.sv"

elaborate -top async_fifo 

clock wr_clk -factor 3
clock rd_clk -factor 4
reset ~wr_rst_n ~rd_rst_n

configure -unlimit proof

prove -all
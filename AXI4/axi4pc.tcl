clear -all
check_cov -init -type all 


analyze -sv "[ glob ./axi4pc.sv]"
analyze -sv "[ glob ./include/*.svh]"
analyze -sv "[ glob ./src/AXI/*.sv]"
analyze -sv "[ glob ./src/*.sv]"

 elaborate -top top

clock clk
reset -none -non_resettable_regs 1

configure -unlimit proof

prove -all
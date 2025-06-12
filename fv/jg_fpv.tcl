clear -all

#
analyze -sv ../rtl/fifo.sv

analyze -sv fv_fifo.sv

elaborate -bbox_a 65535 -bbox_mul 65535 -top fifo

clock clk

reset -expression !arst_n
set_engineJ_max_trace_length 2000

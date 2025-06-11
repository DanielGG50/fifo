clear -all

#
analyze -sv ../rtl/dff.sv
analyze -sv ../rtl/full_adder.sv
analyze -sv ../rtl/ripple_carry_adder.sv

#analyze -sv fv_ripple_carry_adder.sv
#analyze -sv fv_overflow.sv
#analyze -sv fv_a_zero.sv
#analyze -sv fv_b_zero.sv

analyze -sv fv_rca.sv

elaborate -bbox_a 65535 -bbox_mul 65535 -top ripple_carry_adder

clock clk

reset -expression !arst_n
set_engineJ_max_trace_length 2000

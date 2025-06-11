module fv_ripple_carry_adder #(parameter WIDTH = 8, DEPTH = 8) (
  input logic clk,
  input logic rst_n,
  input logic wr_en,
  input logic rd_en,
  input logic [WIDTH-1:0] data_in,
  input logic [WIDTH-1:0] data_out,
  input logic full,
  input logic empty
);

	localparam MAX_VAL = ((1 << WIDTH) * 2) - 1; 
	localparam MSB = WIDTH - 1;


	`define AST(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);
	
	`define ASM(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);



endmodule

bind ripple_carry_adder fv_ripple_carry_adder #(WIDTH, DEPTH) fv_ripple_carry_adder_i(.*);  

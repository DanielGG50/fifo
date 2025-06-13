module fv_fifo #(parameter WIDTH = 8, DEPTH = 8) (
  input logic clk,
  input logic arst_n,
  input logic wr_en,
  input logic rd_en,
  input logic [WIDTH-1:0] data_in,
  input logic [WIDTH-1:0] data_out,
  input logic full,
  input logic empty,
	// Module's internal signals
  logic [$clog2(DEPTH)-1:0] write_ptr,
  logic [$clog2(DEPTH)-1:0] read_ptr,
  logic [$clog2(DEPTH):0] count,
  logic [WIDTH-1:0] fifo_mem [0:DEPTH-1]
);

	`define AST(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);
	
	`define ASM(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_asm_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

	`define COV(block=fifo, name=no_name, precond=1'b1 |->, consq=1'b0) \
	``block``_cov_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);

			// Check writting/reading when not full/empty
  `AST(fifo, write_not_full, wr_en && !full |=>, fifo_mem[$past(write_ptr)] == $past(data_in))
	//`AST(fifo, read_not_empty, rd_en && !empty |=>, data_out == $past(fifo_mem[read_ptr]))

			// Check counter and pointers when writting/reading
  `AST(fifo, write_ptr_increment, wr_en && !full |=>, write_ptr == $past(write_ptr) + 1'b1)
	//`AST(fifo, read_ptr_increment, rd_en && !empty |=>, read_ptr == $past(read_ptr) +  1'b1)
  `AST(fifo, count_increment, wr_en && !full && !empty |=>, count == $past(count) + 1'b1)
	//`AST(fifo, count_decrement, rd_en && !full && !empty |=>, count == $past(count) - 1'b1)

			// Full/Empty flags
	//`AST(fifo, full_flag, count == DEPTH |->, full)
	//`AST(fifo, empty_flag, count == 0 |->, empty)
			// Full empty can not be active at the sema time
	//`AST(fifo, full_not_empty, full |->, !empty)
	//`AST(fifo, empty_not_full, empty |->, !full)


			// Check if write/read block when full/empty
  `AST(fifo, full_invalid_write, (wr_en && full) |=>, $stable(write_ptr) && $stable(count))
	//`AST(fifo, empty_invalid_read, (rd_en && empty) |=>, $stable(read_ptr) && $stable(count))

			// Check if pointer goes back to zero
  //`AST(fifo, w_pointer_wrap, wr_en && write_ptr == DEPTH -  1'b1 |=>, write_ptr == 0)
	//`AST(fifo, r_pointer_wrap, read_ptr == DEPTH -  1'b1 |=>, read_ptr == 0)

			// Check both en_rd and en_wr at the same time
	//`AST(fifo, count_doesnot_move, wr_en && rd_en |=>, $stable(count))  //FIXME This demostrated a bug
	//`AST(fifo,both_pointers_move, wr_en && rd_en && (!full && !empty) |=>, (write_ptr == $past(write_ptr) + 1'b1) && (read_ptr == $past(read_ptr) +  1'b1)) 

			// Asume wr_en or rd_en are deactivated
	//`ASM(fifo, wr_en_deactivated, , wr_en == 1'b0)
	`ASM(fifo, rd_en_deactivated, , rd_en == 1'b0)


endmodule

bind fifo fv_fifo #(WIDTH, DEPTH) fv_fifo_inst (
  .clk(clk),
  .arst_n(arst_n),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .data_in(data_in),
  .data_out(data_out),
  .full(full),
  .empty(empty),

  // Internal signals
  .write_ptr(write_ptr),
  .read_ptr(read_ptr),
  .count(count),
  .fifo_mem(fifo_mem)
); 

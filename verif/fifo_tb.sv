`timescale 1ns/1ps

module fifo_tb;

  localparam WIDTH = 8;
  localparam DEPTH = 8;

  logic clk;
  logic rst_n;
  logic wr_en;
  logic rd_en;
  logic [WIDTH-1:0] data_in;
  logic [WIDTH-1:0] data_out;
  logic full;
  logic empty;

  fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) dut (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .data_in(data_in),
    .data_out(data_out),
    .full(full),
    .empty(empty)
  );

  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    wr_en = 0;
    rd_en = 0;
    data_in = 0;

    #20;
    rst_n = 1;
		// writte until fifo is full
    for (int i = 0; i <= DEPTH + 1; i++) begin
      @(negedge clk);
      wr_en = 1;
      data_in = i;
      rd_en = 0;
      @(posedge clk);
    end

    wr_en = 0;
		// chk
    if (!full) $error("FIFO should be full");

    // Read until fifo is empty
    for (int i = 0; i <= DEPTH + 1; i++) begin
      @(negedge clk);
      rd_en = 1;
      wr_en = 0;
      @(posedge clk);
      if (data_out !== i) $error("Incorrect data, expected %0d, gotten %0d", i, data_out);
    end

    rd_en = 0;

    // Chk
    if (!empty) $error("FIFO should be empty");

    $display("Test finished.");
    $finish;
  end

 	initial begin
		$shm_open("shm_db");
		$shm_probe("ASMTR");
  end

endmodule

module fifo #(parameter WIDTH = 8, parameter DEPTH = 16) (
  input logic clk,
  input logic arst_n,
  input logic wr_en,
  input logic rd_en,
  input logic [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out,
  output logic full,
  output logic empty
);

  (* keep *) logic [WIDTH-1:0] fifo_mem [0:DEPTH-1];
  (* keep *) logic [$clog2(DEPTH)-1:0] write_ptr;
  (* keep *) logic [$clog2(DEPTH)-1:0] read_ptr;
  (* keep *) logic [$clog2(DEPTH):0] count;

  assign full = (count == DEPTH);
  assign empty = (count == 0);

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      write_ptr <= 0;
      read_ptr <= 0;
      count <= 0;
    end else begin
      if (wr_en && !full) begin
        fifo_mem[write_ptr] <= data_in;
        write_ptr <= write_ptr + 1;
        count <= count + 1;
      end
        
      if (rd_en && !empty) begin
        data_out <= fifo_mem[read_ptr];
        read_ptr <= read_ptr + 1;
        count <= count - 1;
      end
    end
  end

endmodule

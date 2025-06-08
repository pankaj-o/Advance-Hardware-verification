// -----------------------------------------------------------------
// Module Name : gray_tb
// Description : Testbench for the 4-bit gray counter (gray.vhd)
// -----------------------------------------------------------------

timeunit 1ns;
timeprecision 1ps;

`define PERIOD 10

module gray_tb;

   logic clk = 0, rst_n = 1, en = 0;
   logic [3:0] dout;
   int delay; 

   gray DUT (.*);
   // gray DUT (.clk(clk), .rst_n(rst_n), .en(en), .dout(dout));

   bind gray gray_sva inst_gray_sva(.*);

   // clock generator
   always clk = #(`PERIOD/2) ~clk;

   // reset task
   task reset_task;
      #(`PERIOD+3 + 5) rst_n <= 1'b0;
      #(`PERIOD*2 + 3) rst_n <= 1'b1;
   endtask

   // enable task
   task enable_task; 
      @(posedge clk) en <= ~en;
   endtask

 
   initial begin
   reset_task(); // Ensure DUT starts in a known state

   repeat(10) begin        
      delay = $urandom_range(10, 1);
      $display("random delay for enable input = %d", delay); 
      #(delay * `PERIOD) enable_task;
   end

   
   $finish;
end

endmodule : gray_tb

// EOF
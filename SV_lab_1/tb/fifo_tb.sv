// ---------------------------------------------------------------------------
// Module Name : fifo_tb
// Description : Testbench for synchronuous FIFO
// ---------------------------------------------------------------------------

`include "fifo_defines.svh"
`include "std_ovl_defines.h"

 module fifo_tb;
 
   logic clk = 0;   
   logic rst_n;
   logic write_n;
   logic read_n;
   logic full;
   logic empty;
   
   logic [`WIDTH-1:0] din;
   logic [`WIDTH-1:0] dout;
   
   int clkcount; 
       
   // Clock generator   
   always #(`PERIOD/2) clk <= ~clk;  
   
   // Clock counter  
   always @(posedge clk) clkcount++; 
   
   // DUT instance   
	sync_fifo # (.B(`B), .W(`W)) 
	DUT (.clk(clk), 
	.rst(~rst_n), 
	.read(~read_n), 
	.write(~write_n), 
	.din (din), 
	.empty(empty), 
	.full(full), 
	.dout (dout));         

   
   
   // Program instance  
	fifo_prog PROG ( 
        .clk(clk),
        .full(full), 
        .empty(empty), 
        .rst_n(rst_n),
        .write_n(write_n), 
        .read_n(read_n), 
        .data(din)
         );  

   
        
   // OVL fifo checker instance		
	ovl_fifo #(.depth(`DEPTH), .width(`WIDTH) , .value_check(1),

	.pass_thru (1), .registered(1), .coverage_level(`OVL_COVER_ALL))

	my_ovl_fifo (
	.clock(clk),
	.reset(rst_n),
	.enable (1),
	.enq(~write_n), 
	.enq_data(din),
	.deq(~read_n),
	.deq_data(dout),
	.full(full),
	.empty(empty),
	.preload(),
	.fire()
);   
	
			      
         
   
   // Additional assertions to check OVERFLOW and UNDERFLOW   
  
 property p_overflow;
      @(posedge clk) disable iff(!rst_n) !write_n |-> !full || (!read_n && full); 
  endproperty
    
 property p_underflow;
      @(posedge clk) disable iff (!rst_n) !read_n |-> !empty || (!write_n && empty);
 endproperty   
   
/* property p_overflow;
      @(posedge clk) disable iff(!rst_n) not(full && !write_n && read_n); 
  endproperty
    
  property p_underflow;
      @(posedge clk) disable iff (!rst_n) not(empty && !read_n && write_n);
  endproperty */
 
 a_overflow : assert property (p_overflow) else
     $warning ("Write to full Fifo!");

 a_underflow: assert property (p_underflow) else
     $warning("Read on empty Fifo!"); 

endmodule

// EOF

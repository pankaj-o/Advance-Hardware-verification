// ---------------------------------------------------------------------------
// Module Name :  fifo_prog
// Description :  Program for Testbench tb_fifo
// --------------------------------------------------------------------------- 

program fifo_prog
	    ( input logic clk,
	      input logic full,
	      input logic empty, 
	      output logic rst_n,
	      output logic write_n,
	      output logic read_n,
	      output logic [7:0] data );
	      
 `include "fifo_env.svh"
 `include "fifo_defines.svh"
	
  default clocking cb @(posedge clk);
  endclocking : cb

  transactions tr;
  driver drv; 
 
   initial begin  
      tr = new;
      drv = new; 
              
      $display("\n T e s t s   a r e   r u n n i n g   . . . \n");  
              
      // ------------------ Directed tests ----------------------- 
      drv.reset; 
      data <= 8'haf;
      ##5 @(negedge clk) write_n <= 0;
      ##(int'(`DEPTH+1)) @(negedge clk) write_n <= 1;
      ##5 @(negedge clk) read_n <= 0;
      ##(int'(`DEPTH+1)) @(negedge clk) read_n <= 1;                       
      data <= 8'hbe;
      ##5 @(negedge clk) write_n <= 0;
      ##(int'(`DEPTH+1)) @(negedge clk) read_n <= 0;
      @(negedge clk) read_n <= 1; write_n <= 1;      
      ##5 @(negedge clk) read_n <= 0;
      ##(int'(`DEPTH+1)) @(negedge clk) write_n <= 0;
      @(negedge clk) read_n <= 1; write_n <= 1;
      
      $display("\nDirected tests are finished.\n");
      // ---------------------------------------------------------                    
      
      // --------------------- Random tests ----------------------
      drv.reset;
      tr.srandom(333);
      repeat(20) begin       
	      assert(tr.randomize());       
	      fork
	        drv.write(tr);
	        drv.read(tr);
 	     join
      end
      
      $display("\nRandom tests are finished.\n");
      // ---------------------------------------------------------
 	         
      drv.reset;
      ##3 $display("\n*** End of simulation. ***\n");	
      
      $finish;
   end 
  
endprogram : fifo_prog

// EOF

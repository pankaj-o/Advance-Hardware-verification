// -----------------------------------------------------------
// File Name    : fifo_env
// Description  : Testbench Classes for FIFO
// -----------------------------------------------------------

`include "fifo_defines.svh"

// input transactions
class transactions;
 
   rand logic [7:0] t_word;
   randc int duration_in;
   randc int duration_out;
   
   constraint dur_i
   { if (!full)
       { duration_in > 0; 
         duration_in <= int'(`DEPTH); } 
      else duration_in == 0; }         
         
   constraint dur_o
   { if (!empty)
       { duration_out > 0; 
         duration_out <= int'(`DEPTH); } 
      else duration_out == 0; }	
      	 
endclass : transactions

// driver class
class driver;      
   // write task
   task write (transactions tr);      
     data <= tr.t_word;
     write_n <= 0;
     ##(tr.duration_in) write_n <= 1;
   endtask : write
      
   // read task
   task read (transactions tr);    
     read_n <= 0;
     ##(tr.duration_out) read_n <= 1;
   endtask : read 
     
   // reset task
   task reset;
      read_n <= 1;
      write_n <= 1;
      rst_n <= 0;
      data <= 0;
      ##5 rst_n <= 1;
   endtask : reset 
   
 endclass : driver 

// EOF

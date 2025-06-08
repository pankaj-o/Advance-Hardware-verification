


// ----------------------------------------------------------------------
// Module Name : gray_sva
// Description : Assertion Module for the 4-bit gray counter (gray.vhd)
// ----------------------------------------------------------------------

timeunit 1ns;
timeprecision 1ps;

module gray_sva (input clk, rst_n, en, [3:0] dout); 
  

// Assertion 1: a_reset - To check the asynchronous reset of the counter
// Note: This must be an immediate assertion!
// insert your code here
	always @(negedge rst_n) begin
	#0 a_reset : assert (dout == 4'b000); 
end

// Assertion 2: a_count_en - To check the enable feature of the counter
// Note: This is a concurrent assertion.


property a_count_enable;
  @(posedge clk) disable iff (!rst_n)
    !en |=> $stable(dout);
endproperty


a_count_en: assert property(a_count_enable);

// Assertion 3: a_gray_check - To check valid gray-encoded transitions 
// Note: This is a concurrent assertion.             
// insert your code here 
property graycheck(dout);
   @(posedge clk) disable iff (!rst_n)

case(dout)
        4'b0000: en |=> dout == 4'b0001;
        4'b0001: en |=> dout == 4'b0011;
        4'b0011: en |=> dout == 4'b0010;
	4'b0010: en |=> dout == 4'b0110;
	4'b0110: en |=> dout == 4'b0111;
	4'b0111: en |=> dout == 4'b0101;
	4'b0101: en |=> dout == 4'b0100;
	4'b0100: en |=> dout == 4'b1100;
	4'b1100: en |=> dout == 4'b1101;
	4'b1101: en |=> dout == 4'b1111;
	4'b1111: en |=> dout == 4'b1110;
	4'b1110: en |=> dout == 4'b1010;
	4'b1010: en |=> dout == 4'b1011;
	4'b1011: en |=> dout == 4'b1001;
	4'b1001: en |=> dout == 4'b1000;
	4'b1000: en |=> dout == 4'b0000;
	endcase
endproperty : graycheck
a_gray_check: assert property(graycheck(dout));

	    
                             

endmodule : gray_sva


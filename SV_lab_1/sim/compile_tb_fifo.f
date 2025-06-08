# Compile file for the fifo testbench
    
# Testbench files
-sv 
+incdir+../tb
../tb/fifo_prog.sv
../tb/fifo_tb.sv
      
# Where to find the OVL library 
-y $STD_OVL_DIR

# File extensions for the OVL library
+libext+.vlib
+libext+.v

# Where to find the OVL include file std_ovl_defines.h
+incdir+$STD_OVL_DIR

# Which macros of the OVL library should be used
+define+OVL_SVA
+define+OVL_ASSERT_ON
+define+OVL_COVER_ON

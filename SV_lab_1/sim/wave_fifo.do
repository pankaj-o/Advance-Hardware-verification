onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fifo_tb/rst_n
add wave -noupdate /fifo_tb/clkcount
add wave -noupdate /fifo_tb/clk
add wave -noupdate /fifo_tb/din
add wave -noupdate /fifo_tb/dout
add wave -noupdate /fifo_tb/write_n
add wave -noupdate /fifo_tb/read_n
add wave -noupdate -expand -group Flags /fifo_tb/full
add wave -noupdate -expand -group Flags /fifo_tb/empty
add wave -noupdate -expand -group Overflow /fifo_tb/a_overflow
add wave -noupdate -expand -group Overflow /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_OVERFLOW_P
add wave -noupdate -expand -group Underflow /fifo_tb/a_underflow
add wave -noupdate -expand -group Underflow /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_UNDERFLOW_P
add wave -noupdate /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_FULL_P
add wave -noupdate /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_EMPTY_P
add wave -noupdate /fifo_tb/my_ovl_fifo/ovl_assert/value_check/A_OVL_FIFO_VALUE_P
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {100150 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 231
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {79853 ps}

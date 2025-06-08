# Script file for SV_lab_1 (fifo)
# It must be started in sim directory 

quit -sim

vcom +cover=bcsef ../rtl/sync_fifo.vhd

vlog -f compile_tb_fifo.f

vopt +acc -o tb_opt fifo_tb

vsim -coverage -assertdebug -onfinish stop -wlfdeleteonquit work.tb_opt

atv log -asserts -enable /fifo_tb/my_ovl_fifo/ovl_assert/A*
atv log -asserts -enable /fifo_tb/my_ovl_fifo/ovl_assert/value_check/A*
atv log -asserts -enable /fifo_tb/a*

view wave
do wave_fifo.do

#add wave /fifo_tb/*

#add wave /fifo_tb/a_overflow
#add wave /fifo_tb/a_underflow

#add wave /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_OVERFLOW_P
#add wave /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_UNDERFLOW_P
#add wave /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_FULL_P
#add wave /fifo_tb/my_ovl_fifo/ovl_assert/A_OVL_FIFO_EMPTY_P
#add wave /fifo_tb/my_ovl_fifo/ovl_assert/value_check/A_OVL_FIFO_VALUE_P

configure wave -signalnamewidth 1

run -all
wave zoomfull

# script run_lab_2.do 
# It must be started in the sim directory

quit -sim
if [file exists "work"] {vdel -all}
vlib work

vcom +cover=bcs ../rtl/gray.vhd
vlog -sv ../tb/gray_tb.sv ../tb/gray_sva.sv  
vopt +acc -o tb_opt gray_tb

vsim -assertdebug -coverage -onfinish stop work.tb_opt

atv log -asserts -enable /gray_tb/DUT/inst_gray_sva/a_count_en
atv log -asserts -enable /gray_tb/DUT/inst_gray_sva/a_gray_check

view wave
add wave /gray_tb/*

add wave /gray_tb/DUT/inst_gray_sva/a_reset
add wave /gray_tb/DUT/inst_gray_sva/a_count_en
add wave /gray_tb/DUT/inst_gray_sva/a_gray_check

configure wave -signalnamewidth 1

run -all
wave zoomfull
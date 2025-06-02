#
# Copyright 2025 Inria
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Authors        Cesar Fuguet
# Creation Date  May, 2025
# Description    Yosys synthesis script
#
source tcl/yosys_common.tcl

set synth_args ""
if { ${param_synth_flatten} } {
  set synth_args "${synth_args} -flatten"
}

set abc_args ""
if { ${param_synth_timing_run} } {
  set abc_args "${abc_args} -liberty ${param_synth_cell_lib_path}"
  set abc_args "${abc_args} -constr ${param_synth_abc_sdc_file_in}"
  set abc_args "${abc_args} -D ${yosys_abc_clk_period}"
}

yosys "read_slang -F ${param_filelist}"
yosys "setattr -set top 1 ${param_top}"
yosys "synth ${synth_args}"
yosys "opt -purge"
yosys "techmap"
yosys "opt"
yosys "dfflibmap -liberty ${param_synth_cell_lib_path}"
yosys "opt"
yosys "opt_dff -sat -nodffe -nosdff"
yosys "dfflegalize"
yosys "clean; check"
yosys "abc ${abc_args}"
yosys "clean; check"
yosys "write_verilog ${param_netlist_dir}/${param_top}.postmap.v"
yosys "tee -o ${param_report_dir}/area.rpt stat -liberty ${param_synth_cell_lib_path}"

# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vthiele_cpu_kami_tb.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Timing enabled?  0/1
VM_TIMING = 1
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 1
# Tracing output mode in VCD format?  0/1 (from --trace)
VM_TRACE_VCD = 1
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vthiele_cpu_kami_tb \
	Vthiele_cpu_kami_tb___024root__DepSet_h39865e8f__0 \
	Vthiele_cpu_kami_tb___024root__DepSet_hc4f13ad1__0 \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_h3109ec6c__0 \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_h3109ec6c__1 \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_hbc6dacae__0 \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_hbc6dacae__1 \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_hbc6dacae__2 \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vthiele_cpu_kami_tb__ConstPool_0 \
	Vthiele_cpu_kami_tb___024root__Slow \
	Vthiele_cpu_kami_tb___024root__DepSet_h39865e8f__0__Slow \
	Vthiele_cpu_kami_tb___024root__DepSet_hc4f13ad1__0__Slow \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__Slow \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_hbc6dacae__0__Slow \
	Vthiele_cpu_kami_tb_thiele_cpu_kami_tb__DepSet_hbc6dacae__1__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \
	Vthiele_cpu_kami_tb__Dpi \
	Vthiele_cpu_kami_tb__Trace__0 \
	Vthiele_cpu_kami_tb__Trace__1 \
	Vthiele_cpu_kami_tb__Trace__2 \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vthiele_cpu_kami_tb__Syms \
	Vthiele_cpu_kami_tb__Trace__0__Slow \
	Vthiele_cpu_kami_tb__TraceDecls__0__Slow \
	Vthiele_cpu_kami_tb__Trace__1__Slow \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \
	verilated_dpi \
	verilated_vcd_c \
	verilated_timing \
	verilated_threads \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-

"""The system top module adds a pin interface and nothing else."""
from __future__ import annotations

import importlib.util
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "kami_system_top.py"
SPEC = importlib.util.spec_from_file_location("kami_system_top", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

PRINTED = """interface Module1;
    method Action loadInstr (Struct1 x_0);
    method Action start ();
    method ActionValue#(Bool) getHalted ();
    method ActionValue#(Bit#(32))
        getMcycleLo ();
endinterface

module mkModule1 (Module1);
    Reg#(Bool) halted <- mkReg(True);
    method Action start ();
        halted <= False;
    endmethod
endmodule

interface Module2;
    method Action rxSample (Bool x_0);
    method ActionValue#(Bool) getTx ();
endinterface

module mkModule2#(function Action loadInstr(Struct1 _), function Action start(),
                  function ActionValue#(Bool) getHalted()) (Module2);
    Reg#(Bool) line <- mkReg(True);
endmodule

module mkThieleSystem (ThieleSystem);
    Module1 m1 <- mkModule1 ();
    Module2 m2 <- mkModule2 (m1.loadInstr, m1.start,
        m1.getHalted);
endmodule
"""


def test_exports_exactly_the_outermost_module():
    out = MODULE.build(PRINTED, "ThieleSystem")
    ifc = out[out.index("interface ThieleSystem;"):]
    ifc = ifc[:ifc.index("endinterface")]
    assert "rxSample" in ifc and "getTx" in ifc
    # The loader calls into the CPU, so none of the CPU's methods are pins.
    for inner in ("loadInstr", "start ()", "getHalted", "getMcycleLo"):
        assert inner not in ifc


def test_forwards_and_keeps_the_printed_instances():
    out = MODULE.build(PRINTED, "ThieleSystem")
    assert "Module2 m2 <- mkModule2 (m1.loadInstr, m1.start, m1.getHalted);" in out
    assert "m2.rxSample(x_0);" in out
    assert "let r <- m2.getTx();" in out
    assert "m1.getMcycleLo" not in out
    assert out.count("(* synthesize *)") == 2
    assert "(* synthesize *)\nmodule mkModule1" in out


def test_module_bodies_are_untouched():
    out = MODULE.build(PRINTED, "ThieleSystem")
    for line in ("Reg#(Bool) halted <- mkReg(True);", "halted <= False;",
                 "Reg#(Bool) line <- mkReg(True);"):
        assert line in out

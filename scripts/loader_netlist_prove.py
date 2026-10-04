#!/usr/bin/env python3
"""Reset and induction proof of the board/loader against the routed netlist.

The CPU response ports are an explicit shared interface, not a proved CPU.
All board outputs, live instruction bits, and both CPU method enables are
compared. Internal register observations and proved one-hot invariants make
the relation inductive. Both the reset base and arbitrary step must pass.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu/hardware/rtl"
TOP = "thiele_cpu_top_genesys2"
RTL_FILES = ("RegFile.v", "thiele_cpu_kami.v", "thiele_system.v", "thiele_cpu_top_genesys2.v")
BOARD_CELLS = ("ibufds_sysclk", "mmcm_cpu", "bufg_cpu")
RESPONSES = {"getPC": 32, "getMu": 32, "getErr": 1, "getHalted": 1,
             "getCertified": 1, "getErrorCode": 32, "RDY_loadInstr": 1}
UNUSED_INSTRUCTION_BITS = {53, 62, 71}
FF_TYPES = {"$dff", "$dffe", "$sdff", "$sdffe", "$sdffce", "$adff", "$adffe"}
SUCCESS = "SAT proof finished - no model found: SUCCESS!"


def quoted(path: Path) -> str:
    return '"' + path.resolve().as_posix() + '"'


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interface_manifest(top: dict) -> dict:
    """Reject an unexpected boundary instead of silently losing comparisons."""
    nets = top["netnames"]
    seen: set[int] = set()
    for name, width in RESPONSES.items():
        bits = nets[f"system.m1${name}"]["bits"]
        if len(bits) != width or not all(isinstance(b, int) for b in bits):
            raise ValueError(f"unexpected CPU response representation: {name}")
        if seen.intersection(bits):
            raise ValueError(f"CPU response ports share bits: {name}")
        if name != "getErrorCode" and len(set(bits)) != len(bits):
            raise ValueError(f"unexpected response aliases: {name}")
        seen.update(bits)
    bus = nets["system.m1$loadInstr_x_0"]["bits"]
    if len(bus) != 135:
        raise ValueError("instruction interface width changed")
    used = {b for cell in top["cells"].values() for port, bits in cell["connections"].items()
            if cell["port_directions"][port] == "input" for b in bits}
    live = [i for i, b in enumerate(bus) if b in used or isinstance(b, str)]
    omitted = set(range(135)) - set(live)
    if omitted != UNUSED_INSTRUCTION_BITS:
        raise ValueError(f"instruction connectivity changed: unconnected bits {sorted(omitted)}")
    # Repeated error-code bits are actual aliases in the physical netlist.
    # Use that same representation on both sides of the shared interface.
    error = nets["system.m1$getErrorCode"]["bits"]
    representative = {b: i for i, b in enumerate(error)}
    return {"response_widths": RESPONSES, "error_code_representatives": [representative[b] for b in error],
            "instruction_width": 135, "compared_instruction_bits": live,
            "unconnected_instruction_bits": sorted(omitted)}


def boundary_script(interface: dict) -> str:
    boundary = " ".join(f"{TOP}/w:system.m1${name}" for name in RESPONSES)
    # These are assignments to NEW, undriven observation/input wires. They do
    # not rewrite drivers of RTL state. -nomap/-nounset avoids rescanning the
    # entire flattened FPGA for each bit of an observation bus.
    observe = "\n".join(f"connect -nomap -nounset -set loader_write_data[{j}] system.m1$loadInstr_x_0[{i}]"
                        for j, i in enumerate(interface["compared_instruction_bits"]))
    aliases = "\n".join(f"connect -nomap -nounset -set system.m1$getErrorCode.i[{i}] boundary_error[{rep}]"
                        for i, rep in enumerate(interface["error_code_representatives"]))
    return f"""cd {TOP}
add -output loader_write_data {len(interface['compared_instruction_bits'])}
{observe}
cd ..
expose {TOP}/w:system.m1$EN_loadInstr {TOP}/w:system.m1$EN_start
expose -cut {TOP}/w:cpu_clk {boundary}
delete -output {TOP}/w:cpu_clk {boundary}
cd {TOP}
add -input boundary_error 32
delete -port system.m1$getErrorCode.i
{aliases}
cd ..
opt_clean -purge
check -assert
"""


def prepare_script(netlist: Path, work: Path, interface: dict,
                   yosys_share: Path | None = None) -> str:
    def library(name: str) -> str:
        return quoted(yosys_share / "xilinx" / name) if yosys_share else f"+/xilinx/{name}"

    rtl = " ".join(quoted(RTL / name) for name in RTL_FILES)
    delete = " ".join(f"{TOP}/{name}" for name in BOARD_CELLS)
    cuts = boundary_script(interface)
    return f"""read_verilog -lib {library('cells_xtra.v')}
read_verilog -sv -DSYNTHESIS {rtl}
hierarchy -top {TOP}
proc
flatten
delete {delete}
{cuts}
opt_expr
opt_clean
opt -nodffe -nosdff
fsm
opt
memory -nomap
opt_clean -purge
check -assert
design -stash gold
read_json {quoted(netlist)}
read_verilog -overwrite {library('cells_sim.v')}
hierarchy -top {TOP}
delete {delete}
proc
flatten
{cuts}
memory -nomap
opt_clean -purge
check -assert
design -stash gate
design -copy-from gold -as gold {TOP}
design -copy-from gate -as gate {TOP}
write_json {quoted(work / 'prepared.json')}
"""


def driven_bits(module: dict) -> set:
    return ({"0", "1"} |
            {b for c in module["cells"].values() for p, bits in c["connections"].items()
             if c["port_directions"][p] == "output" for b in bits} |
            {b for p in module["ports"].values() if p["direction"] == "input" for b in p["bits"]})


def register_bits(module: dict) -> set:
    return {b for c in module["cells"].values() if c["type"] in FF_TYPES
            for b in c["connections"]["Q"]}


def add_observations(data: dict, interface: dict) -> dict:
    gold, gate = (data["modules"][name] for name in ("gold", "gate"))
    expected_inputs = {"clk_p": 1, "clk_n": 1, "cpu_reset_n": 1, "uart_rx": 1,
                       "cpu_clk.i": 1, "boundary_error": 32}
    expected_inputs.update({f"system.m1${n}.i": width for n, width in RESPONSES.items()
                            if n != "getErrorCode"})
    expected_outputs = {"uart_tx": 1, "LED_HALTED": 1, "LED_ERR": 1, "LED_BIANCHI": 1,
                        "LED_LOADING": 1, "loader_write_data": len(interface["compared_instruction_bits"]),
                        "system.m1$EN_start": 1, "system.m1$EN_loadInstr": 1}
    for module in (gold, gate):
        for direction, expected in (("input", expected_inputs), ("output", expected_outputs)):
            actual = {n: len(p["bits"]) for n, p in module["ports"].items() if p["direction"] == direction}
            if actual != expected:
                raise ValueError(f"unexpected prepared {direction} ports: {actual}")
        reset_name = "rst_n" if "rst_n" in module["netnames"] else "system.RST_N"
        for name, width in (("por_count", 5), (reset_name, 1)):
            wire = module["netnames"][name]
            if len(wire["bits"]) != width or wire["attributes"].get("init") != "0" * width:
                raise ValueError(f"power-on initialization changed: {name}")
        reset = module["netnames"][reset_name]["bits"]
        module["ports"]["observe_board_reset"] = {"direction": "output", "bits": reset}
        module["netnames"]["observe_board_reset"] = {"hide_name": 0, "bits": reset, "attributes": {}}

    gq, tq = register_bits(gold), register_bits(gate)
    gd, td = driven_bits(gold), driven_bits(gate)
    observations = []
    # Register aliases matter: the request flags survive as the corresponding
    # acknowledge register's D_IN name, not their original declaration names.
    for name in sorted(gold["netnames"].keys() & gate["netnames"].keys()):
        gb, tb = gold["netnames"][name]["bits"], gate["netnames"][name]["bits"]
        if name != "por_count" and not (name.startswith("system.m2_") and
                                        any(a in gq and b in tq for a, b in zip(gb, tb))):
            continue
        if len(gb) != len(tb):
            raise ValueError(f"register observation width differs: {name}")
        indices = [i for i, (a, b) in enumerate(zip(gb, tb)) if a in gd and b in td]
        if not indices:
            continue
        observations.append({"name": name, "indices": indices,
                             "unused_indices": sorted(set(range(len(gb))) - set(indices))})
        port = "observe_" + name.replace(".", "_")
        for module in (gold, gate):
            bits = [module["netnames"][name]["bits"][i] for i in indices]
            module["ports"][port] = {"direction": "output", "bits": bits}
            module["netnames"][port] = {"hide_name": 0, "bits": bits, "attributes": {}}
    if not observations:
        raise ValueError("no register observations")
    return {"external_outputs": expected_outputs, "register_observations": observations}


def make_harness(data: dict) -> str:
    gold, gate = (data["modules"][name] for name in ("gold", "gate"))
    if gold["ports"].keys() != gate["ports"].keys():
        raise ValueError("component ports differ")
    inputs = {n: p for n, p in gold["ports"].items() if p["direction"] == "input"}
    outputs = {n: p for n, p in gold["ports"].items() if p["direction"] == "output"}
    lines, g, t, equal = ["module component_proof;"], [], [], []
    for i, (name, port) in enumerate(inputs.items()):
        lines.append(f'(* anyseq *) reg [{len(port["bits"])-1}:0] in_{i};')
        g.append(f'.\\{name} (in_{i})')
        t.append(f'.\\{name} (in_{i})')
        if name == "cpu_clk.i":
            clock = f"in_{i}"
    for i, (name, port) in enumerate(outputs.items()):
        lines.append(f'wire [{len(port["bits"])-1}:0] g_{i}, t_{i};')
        g.append(f'.\\{name} (g_{i})')
        t.append(f'.\\{name} (t_{i})')
        equal.append(f"(g_{i} == t_{i})")
        if name == "observe_por_count":
            por = (f"g_{i}", f"t_{i}")
        if name == "observe_board_reset":
            reset = (f"g_{i}", f"t_{i}")
    for i, name in enumerate(("system.m2_ld_phase", "system.m2_rx_state")):
        bits = gold["netnames"][name]["bits"]
        if len(bits) != 4:
            raise ValueError(f"one-hot FSM encoding changed: {name}")
        port = f"aux_phase_{i}"
        gold["ports"][port] = {"direction": "output", "bits": bits}
        gold["netnames"][port] = {"hide_name": 0, "bits": bits, "attributes": {}}
        lines.append(f"wire [3:0] {port};")
        g.append(f".{port}({port})")
        equal.append("(" + " || ".join(f"{port} == 4'd{v}" for v in (1, 2, 4, 8)) + ")")
    lines += ["gold gold_impl(" + ", ".join(g) + ");", "gate gate_impl(" + ", ".join(t) + ");",
              "wire invariant = " + " && ".join(equal) + ";", "reg past = 0;", "reg invariant_q;",
              f"always @(posedge {clock}) begin past <= 1; invariant_q <= invariant; end",
              "`ifdef BASE", "always @* if (!past) begin",
              f"assume({por[0]} == 0); assume({por[1]} == 0);",
              f"assume({reset[0]} == 0); assume({reset[1]} == 0);", "end", "`endif",
              "always @* if (past) begin", "`ifndef BASE", "assume(invariant_q);", "`endif",
              "assert(invariant);", "end", "endmodule"]
    return "\n".join(lines) + "\n"


def proof_script(work: Path, mode: str, lower_checks: bool, timeout: int) -> str:
    if mode not in ("base", "step"):
        raise ValueError("unknown proof obligation")
    define = "-DBASE" if mode == "base" else ""
    return f"""read_json {quoted(work / 'models.json')}
read_verilog -formal {define} {quoted(work / 'component-proof.v')}
prep -flatten -top component_proof
{'chformal -lower' if lower_checks else ''}
async2sync
dffunmap
setattr -unset init component_proof/w:*
setattr -set init 1'b0 component_proof/w:past
check -assert
select -assert-count 1 component_proof/t:$assert
sat -seq 2 -set-assumes -prove-asserts -verify -timeout {timeout} -dump_vcd {quoted(work / (mode + '.vcd'))}
"""


def execute(yosys: str, work: Path, name: str, script: str, timeout: int, proof: bool) -> dict:
    script_file, log = work / f"{name}.ys", work / f"{name}.log"
    script_file.write_text(script, encoding="utf-8", newline="\n")
    started = time.monotonic()
    status, code = "ERROR", None
    with (work / f"{name}.console.log").open("w", encoding="utf-8") as output:
        try:
            proc = subprocess.run([yosys, "-ql", str(log), "-s", str(script_file)], cwd=work,
                                  stdout=output, stderr=subprocess.STDOUT, timeout=timeout + 60)
            code = proc.returncode
            text = log.read_text(encoding="utf-8", errors="replace") if log.exists() else ""
            clean = "Found and reported 0 problems." in text
            conflict = "Driver-driver conflict" in text or "multiple conflicting drivers" in text
            status = "PASS" if code == 0 and clean and not conflict and (not proof or SUCCESS in text) else "FAIL"
        except subprocess.TimeoutExpired:
            status = "TIMEOUT"
    result = {"name": name, "status": status, "exit_code": code,
              "seconds": round(time.monotonic() - started, 3), "log": log.name,
              "script_sha256": digest(script_file)}
    print(f"[loader-equivalence] {name}: {status}", flush=True)
    return result


def complete(results: list[dict]) -> bool:
    return (len(results) == 3 and {r["name"] for r in results} == {"prepare", "base", "step"}
            and all(r["status"] == "PASS" for r in results))


def prove(netlist: Path, report_file: Path, *, yosys: str = "yosys",
          yosys_share: Path | None = None, timeout: int = 900) -> bool:
    work = report_file.parent.resolve() / "loader-equivalence"
    work.mkdir(parents=True, exist_ok=True)
    report_file.parent.mkdir(parents=True, exist_ok=True)
    report = {"status": "INCOMPLETE", "equivalent": False, "component_equivalent": False,
              "scope": "board and loader, conditional on equal CPU response interfaces",
              "unproved_components": ["CPU RTL/netlist equivalence", "RAM RTL/netlist equivalence",
                                      "analog clock behavior and physical timing"],
              "obligations": [], "method": "reset base and arbitrary one-step induction"}

    def save() -> None:
        temporary = report_file.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(report_file)

    save()
    try:
        interface = interface_manifest(json.loads(netlist.read_text(encoding="utf-8"))["modules"][TOP])
        report["interface"] = interface
        report["yosys"] = subprocess.run([yosys, "-V"], capture_output=True, text=True, check=True).stdout.strip()
        formal_help = subprocess.run([yosys, "-Q", "-T", "-p", "help chformal"],
                                     capture_output=True, text=True, check=True).stdout
        lower_checks = "-lower" in formal_help
        report["inputs"] = {str(p): digest(p) for p in [netlist, Path(__file__).resolve()] +
                            [RTL / name for name in RTL_FILES]}
        result = execute(yosys, work, "prepare", prepare_script(netlist, work, interface, yosys_share), timeout, False)
        report["obligations"].append(result)
        save()
        if result["status"] == "PASS":
            models = json.loads((work / "prepared.json").read_text(encoding="utf-8"))
            report["observations"] = add_observations(models, interface)
            report["compared_bits"] = sum(len(p["bits"]) for p in models["modules"]["gold"]["ports"].values()
                                          if p["direction"] == "output")
            (work / "component-proof.v").write_text(make_harness(models), encoding="utf-8", newline="\n")
            (work / "models.json").write_text(json.dumps(models), encoding="utf-8")
            report["model_sha256"] = digest(work / "models.json")
            report["harness_sha256"] = digest(work / "component-proof.v")
            for mode in ("base", "step"):
                report["obligations"].append(execute(yosys, work, mode,
                    proof_script(work, mode, lower_checks, timeout), timeout, True))
                save()
        ok = complete(report["obligations"])
        report["status"] = "PASS" if ok else "FAIL"
        report["component_equivalent"] = ok
        save()
        return ok
    except Exception as exc:
        report["status"] = "ERROR"
        report["error"] = str(exc)
        save()
        raise

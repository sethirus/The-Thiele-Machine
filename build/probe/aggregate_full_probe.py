#!/usr/bin/env python3
"""Aggregate full-corpus Print Assumptions output into pinned artifacts."""
import hashlib
import datetime
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path("/workspaces/The-Thiele-Machine")
BUILD = ROOT / "build" / "probe"
RAW = BUILD / "probe_all_output.txt"
ERR = BUILD / "probe_all_err.txt"
INV = BUILD / "probe_inventory.json"
ART = ROOT / "artifacts"
ART.mkdir(exist_ok=True)

inv = json.loads(INV.read_text())
queries = []
for f in inv["files"]:
    for t in f["addressable"]:
        queries.append({
            "file": f["file"],
            "qualified_module": f["qualified_module"],
            "local_name": t["local_name"],
            "kind": t["kind"],
            "full_name": t["full_name"],
            "via": "direct",
        })
for ex in inv.get("extras_addressable_via_instantiation", []):
    queries.append({
        "file": ex.get("instantiation_site", ""),
        "qualified_module": ex["full_name"].rsplit(".", 1)[0],
        "local_name": ex["full_name"].rsplit(".", 1)[1],
        "kind": "Theorem",
        "full_name": ex["full_name"],
        "via": "functor_instantiation",
        "source_functor": ex["source_functor"],
    })

text = RAW.read_text(errors="replace")
err_text = ERR.read_text(errors="replace")
lines = text.splitlines()

blocks = []
unexpected = []
i, n = 0, len(lines)
while i < n:
    line = lines[i]
    if line == "Closed under the global context":
        blocks.append({"closed": True, "axioms": []})
        i += 1
    elif line == "Axioms:":
        i += 1
        axioms_raw = []
        while i < n and lines[i] not in ("Closed under the global context", "Axioms:"):
            axioms_raw.append(lines[i])
            i += 1
        axioms = []
        cur_name, cur_type = None, []
        for ln in axioms_raw:
            if ln and not ln.startswith(" ") and not ln.startswith("\t"):
                if cur_name is not None:
                    axioms.append({"name": cur_name,
                                   "type": " ".join(s.strip() for s in cur_type).strip()})
                if " : " in ln:
                    nm, ty = ln.split(" : ", 1)
                    cur_name, cur_type = nm.strip(), [ty]
                else:
                    cur_name, cur_type = ln.strip(), []
            else:
                cur_type.append(ln)
        if cur_name is not None:
            axioms.append({"name": cur_name,
                           "type": " ".join(s.strip() for s in cur_type).strip()})
        blocks.append({"closed": False, "axioms": axioms})
    else:
        if line.strip():
            unexpected.append({"line_no": i + 1, "text": line[:240]})
        i += 1

print(f"queries={len(queries)} blocks={len(blocks)} unexpected={len(unexpected)}", file=sys.stderr)

STDLIB_PREFIXES = (
    "Coq.", "ClassicalDedekindReals.", "FunctionalExtensionality.",
    "Classical_Prop.", "Classical_Pred_Type.", "ClassicalEpsilon.",
    "ClassicalChoice.", "ClassicalUniqueChoice.", "ClassicalDescription.",
    "ProofIrrelevance.", "PropExtensionality.", "PropExtensionalityFacts.",
    "Eqdep.", "JMeq.", "Streams.",
)
STDLIB_AXIOMS = {
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "FunctionalExtensionality.functional_extensionality",
    "Classical_Prop.classic",
    "Classical_Pred_Type.classic_dec_pred",
    "ClassicalEpsilon.constructive_indefinite_description",
    "ClassicalChoice.choice",
    "Eqdep.Eq_rect_eq.eq_rect_eq",
    "JMeq.JMeq_eq",
    "ProofIrrelevance.proof_irrelevance",
    "PropExtensionalityFacts.PropExt",
    "PropExtensionality.propositional_extensionality",
}


def classify(name):
    if name in STDLIB_AXIOMS:
        return "stdlib"
    if any(name.startswith(p) for p in STDLIB_PREFIXES):
        return "stdlib"
    return "user_or_third_party"


pairs = list(zip(queries, blocks))

all_axioms = Counter()
per_file = defaultdict(lambda: {"theorems": 0, "closed": 0, "with_axioms": 0,
                                "axiom_set": set()})
per_namespace = defaultdict(lambda: {"theorems": 0, "closed": 0, "with_axioms": 0,
                                     "axiom_set": set()})
per_theorem_results = []
non_stdlib_findings = []
classical_users = []
funext_users = []
real_completeness_users = []

for q, b in pairs:
    file_key = q["file"]
    ns = q["qualified_module"].split(".")[0]
    pf = per_file[file_key]
    pn = per_namespace[ns]
    pf["theorems"] += 1
    pn["theorems"] += 1
    if b["closed"]:
        pf["closed"] += 1
        pn["closed"] += 1
        per_theorem_results.append({
            "full_name": q["full_name"], "file": file_key, "kind": q["kind"],
            "via": q.get("via", "direct"), "status": "closed_under_global_context", "axioms": [],
        })
    else:
        pf["with_axioms"] += 1
        pn["with_axioms"] += 1
        names = sorted(set(a["name"] for a in b["axioms"]))
        for nm in names:
            all_axioms[nm] += 1
            pf["axiom_set"].add(nm)
            pn["axiom_set"].add(nm)
        classes = {classify(nm) for nm in names}
        per_theorem_results.append({
            "full_name": q["full_name"], "file": file_key, "kind": q["kind"],
            "via": q.get("via", "direct"), "status": "depends_on_axioms",
            "axioms": names, "axiom_classes": sorted(classes),
        })
        if "user_or_third_party" in classes:
            non_stdlib_findings.append({
                "full_name": q["full_name"], "file": file_key, "axioms": names,
            })
        if "Classical_Prop.classic" in names:
            classical_users.append(q["full_name"])
        if any("functional_extensionality" in nm for nm in names):
            funext_users.append(q["full_name"])
        if any("ClassicalDedekindReals" in nm for nm in names):
            real_completeness_users.append(q["full_name"])

for d in (per_file, per_namespace):
    for k, v in d.items():
        v["axiom_set"] = sorted(v["axiom_set"])

# Pin raw output (kept identical to coqc stdout)
raw_dest = ART / "print_assumptions_all_proofs.txt"
raw_dest.write_text(text)

csv_dest = ART / "print_assumptions_all_proofs.csv"
with open(csv_dest, "w") as f:
    f.write("full_name,file,kind,via,status,axioms\n")
    for r in per_theorem_results:
        ax = "|".join(r["axioms"])
        f.write(f"{r['full_name']},{r['file']},{r['kind']},{r['via']},{r['status']},{ax}\n")

unaddressable_listing = []
for f in inv["files"]:
    for u in f["unaddressable"]:
        unaddressable_listing.append({
            "full_name_unaddressable": u["full_name_unaddressable"],
            "kind": u["kind"], "reason": u["reason"], "file": f["file"],
        })

closed_count = sum(1 for r in per_theorem_results if r["status"] == "closed_under_global_context")
axiom_count = sum(1 for r in per_theorem_results if r["status"] == "depends_on_axioms")

manifest = {
    "schema": "thiele-print-assumptions-full-probe-v2",
    "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "coq_version": "8.18.0",
    "probe_file": "coq/AssumptionsProbeAll.v",
    "raw_output_file": "artifacts/print_assumptions_all_proofs.txt",
    "raw_output_sha256": hashlib.sha256(text.encode()).hexdigest(),
    "files_probed": inv["files_probed"],
    "addressable_theorems_probed": len(queries),
    "blocks_parsed": len(blocks),
    "alignment_ok": len(blocks) == len(queries),
    "stderr_nonempty": bool(err_text.strip()),
    "stderr_excerpt": err_text[:1000] if err_text.strip() else "",
    "unexpected_lines_in_output": len(unexpected),
    "first_unexpected_lines": unexpected[:20],
    "summary": {
        "theorems_probed": len(queries),
        "closed_under_global_context": closed_count,
        "depend_on_axioms": axiom_count,
        "user_or_third_party_axiom_findings": len(non_stdlib_findings),
        "excluded_middle_users": len(classical_users),
        "functional_extensionality_users": len(funext_users),
        "real_completeness_axiom_users": len(real_completeness_users),
        "unique_axioms_used": dict(sorted(all_axioms.items(), key=lambda kv: -kv[1])),
    },
    "user_or_third_party_axiom_findings": non_stdlib_findings,
    "classical_logic_users": classical_users,
    "unaddressable_theorems_in_functors_or_module_types": unaddressable_listing,
    "by_namespace": {ns: v for ns, v in sorted(per_namespace.items())},
    "by_file": {fk: v for fk, v in sorted(per_file.items())},
}

manifest_dest = ART / "print_assumptions_all_proofs.json"
manifest_dest.write_text(json.dumps(manifest, indent=2))

print(f"Wrote {raw_dest}")
print(f"Wrote {csv_dest}")
print(f"Wrote {manifest_dest}")
print()
print("=== SUMMARY ===")
print(f"  Files probed:                       {manifest['files_probed']}")
print(f"  Addressable theorems probed:        {len(queries)}")
print(f"  Blocks parsed (alignment_ok={manifest['alignment_ok']})")
print(f"  Closed under global context:        {closed_count}")
print(f"  Depend on stdlib axioms:            {axiom_count}")
print(f"  USER/THIRD-PARTY axiom findings:    {len(non_stdlib_findings)}")
print(f"  Excluded-middle users:              {len(classical_users)}")
print(f"  Functional extensionality users:    {len(funext_users)}")
print(f"  Real-completeness users:            {len(real_completeness_users)}")
print(f"  Unaddressable (functor/sig):        {len(unaddressable_listing)}")
print()
print("=== UNIQUE AXIOMS (top 20 by use count) ===")
for name, ct in list(sorted(all_axioms.items(), key=lambda kv: -kv[1]))[:20]:
    cls = classify(name)
    flag = "   " if cls == "stdlib" else "[*]"
    print(f"  {flag} {ct:6d}  {name}")
if non_stdlib_findings:
    print()
    print("=== USER/THIRD-PARTY AXIOM FINDINGS (first 30) ===")
    for f_ in non_stdlib_findings[:30]:
        print(f"  {f_['full_name']}: {f_['axioms']}")
else:
    print()
    print("=== USER/THIRD-PARTY AXIOMS: none ===")

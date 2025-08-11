# the_final_proof.py
# Final contest: Integer vs Golden Ratio
# Compares W >= 2*K and W >= phi*K against the fossil record

import math

# Golden Ratio
phi = 1.61803398875

# Fossil record (replace with full data as needed)
FOSSIL_RECORD = """
name,W,K,d,T
Axiom of Blindness,10.0,184,1,1
Game of Life,900.0,264,4,2
Lensing,0.0,0,2,2
N-Body and FLRW,0.0,0,2,2
Phyllotaxis,0.0,0,2,2
Mandelbrot,5444.0,312,50,2
Universality,0.0,0,2,2
The Thiele Machine,0.0,0,2,2
NUSD Law,0.0,0,2,2
Universality Demonstration,0.0,0,2,2
Physical Realization,0.0,0,2,2
Scale Comparison,0.0,0,2,2
Capstone Demonstration,0.0,0,2,2
Process Isomorphism,0.0,0,2,2
Geometric Logic,0.0,0,2,2
Finite Bounded-Step Halting Experiments,0.0,0,2,2
Geometry of Truth,112.0,264,1,4
Geometry of Coherence,0.0,0,2,2
Conclusion,0.0,0,2,2
"""

def parse_master_log(log):
    lines = [l.strip() for l in log.strip().split('\n') if l.strip()]
    header = lines[0].split(',')
    records = []
    for line in lines[1:]:
        fields = line.split(',')
        record = {header[i]: float(fields[i]) if i > 0 else fields[i] for i in range(len(fields))}
        records.append(record)
    return records

def audit_law(records, law_name, law_func):
    results = []
    for rec in records:
        W = rec['W']
        K = rec['K']
        verdict = W >= law_func(K)
        results.append((rec['name'], W, K, verdict))
    return results

def print_audit(results, law_name):
    print(f"\nAudit for {law_name}:")
    pass_count = 0
    fail_count = 0
    for name, W, K, verdict in results:
        status = "PASS" if verdict else "FAIL"
        print(f"{name}: W={W:.2f} >= {law_name}({K:.2f})? {status}")
        if verdict:
            pass_count += 1
        else:
            fail_count += 1
    print(f"\nSummary for {law_name}: {pass_count} PASS, {fail_count} FAIL")

def main():
    print("="*60)
    print("THE FINAL PROOF: Integer vs Golden Ratio")
    print("="*60)
    records = parse_master_log(FOSSIL_RECORD)
    law_2 = lambda K: 2 * K
    law_phi = lambda K: phi * K
    results_2 = audit_law(records, "2*K", law_2)
    results_phi = audit_law(records, "phi*K", law_phi)
    print_audit(results_2, "2*K")
    print_audit(results_phi, "phi*K")
    print("\nWhich law leaves fewer paradoxes? The answer is above.")

if __name__ == "__main__":
    main()
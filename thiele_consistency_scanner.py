# thiele_consistency_scanner.py
# Scans parameter space for inconsistencies in the Thiele Law

import numpy as np

# Empirical coefficients
c0 = 10.24   # increased by 8.0 more
c1 = 1.24
c2 = 0.0
c3 = -0.30
c4 = 0.10
c5 = 10.69   # increased by 8.0 more

def thiele_rhs(K, d, T, L):
    return K * (c0 + c1*d + c2*d**2 + c3*T + c4*L + c5)

def scan_space(K_range, d_range, T_range, L_map):
    inconsistencies = []
    for K in K_range:
        for d in d_range:
            for T in T_range:
                L = L_map.get(T, 0)
                rhs = thiele_rhs(K, d, T, L)
                if rhs < 0:
                    inconsistencies.append({'K': K, 'd': d, 'T': T, 'L': L, 'rhs': rhs})
    return inconsistencies

def main():
    print("="*60)
    print("Thiele Law Consistency Scanner")
    print("="*60)
    K_range = range(1, 101)
    d_range = range(1, 101)
    T_range = [1, 3, 7]
    L_map = {1: 1, 3: 2, 7: 3}
    inconsistencies = scan_space(K_range, d_range, T_range, L_map)
    if inconsistencies:
        print(f"Found {len(inconsistencies)} inconsistent cases (rhs < 0):")
        for inc in inconsistencies[:20]:
            print(f"K={inc['K']}, d={inc['d']}, T={inc['T']}, L={inc['L']}, rhs={inc['rhs']:.2f}")
        print("...")
        print("Suggest: Restrict d, T, K, or revise coefficients to ensure rhs >= 0.")
    else:
        print("No inconsistencies found. Law is consistent for scanned ranges.")

if __name__ == "__main__":
    main()
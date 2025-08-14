# thiele_auto_consistency.py
# Automates finding minimum rhs and required W_min for Thiele Law consistency

import numpy as np

# Initial coefficients
c0 = 10.24
c1 = 1.24
c2 = 0.0
c3 = -0.30
c4 = 0.10
c5 = 10.69

def thiele_rhs(K, d, T, L):
    return K * (c0 + c1*d + c2*d**2 + c3*T + c4*L + c5)

def scan_max_rhs(K_range, d_range, T_range, L_map):
    max_rhs = float('-inf')
    max_case = None
    for K in K_range:
        for d in d_range:
            for T in T_range:
                L = L_map.get(T, 0)
                rhs = thiele_rhs(K, d, T, L)
                if rhs > max_rhs:
                    max_rhs = rhs
                    max_case = {'K': K, 'd': d, 'T': T, 'L': L, 'rhs': rhs}
    # Scan d as float for finer maximum
    for K in K_range:
        for d in np.arange(1, 100.001, 0.001):
            for T in T_range:
                L = L_map.get(T, 0)
                rhs = thiele_rhs(K, d, T, L)
                if rhs > max_rhs:
                    max_rhs = rhs
                    max_case = {'K': K, 'd': d, 'T': T, 'L': L, 'rhs': rhs}
    return max_rhs, max_case

def main():
    print("="*60)
    print("Thiele Law Auto-Consistency Finder")
    print("="*60)
    K_range = range(1, 101)
    d_range = range(1, 101)
    T_range = [1, 3, 7]
    L_map = {1: 1, 3: 2, 7: 3}
    max_rhs, max_case = scan_max_rhs(K_range, d_range, T_range, L_map)
    print(f"Maximum rhs found: {max_rhs:.2f} at {max_case}")
    W_min = int(np.ceil(max_rhs))
    print(f"Suggested minimal W for consistency: W_min = {W_min}")
    print("Update your proof to require W >= W_min for all processes.")

if __name__ == "__main__":
    main()
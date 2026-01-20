import numpy as np

def check_inequalities():
    count = 0
    violations_1 = 0
    violations_2 = 0
    
    for _ in range(100000):
        # Generate random matrix
        A = np.random.randn(5, 5)
        M = A @ A.T
        # Normalize diagonal
        d = np.sqrt(np.diag(M))
        M = M / np.outer(d, d)
        
        # Check inequality 1: 1 - M13^2 - 2*M14^2 + 2*M14^2*M13 >= 0
        # Indices 0-based: 1=A0, 3=B0, 4=B1. M[1,3], M[1,4]
        # M is symmetric.
        x = M[1,3]
        y = M[1,4]
        
        val1 = 1 - x**2 - 2*y**2 + 2*(y**2)*x
        if val1 < -1e-9:
            violations_1 += 1
            if violations_1 == 1:
                print(f"Violation 1: x={x}, y={y}, val={val1}")
                # Check eigenvalues of submatrix {1,3,4}
                sub = M[np.ix_([1,3,4],[1,3,4])]
                print("Submatrix eig:", np.linalg.eigvalsh(sub))

        # Check inequality 2: 1 - M23^2 - M24^2 - M34^2 + 2*M24*M34*M23 >= 0
        # Wait, let's copy the text exactly for inequality 2
        # 1 - (M i2 i3)*(M i2 i3) - (M i2 i4)*(M i2 i4) - (M i3 i4)*(M i3 i4) + 2*(M i2 i4)*(M i3 i4)*(M i2 i3) >= 0.
        # Indices: 2, 3, 4. (A1, B0, B1).
        # x = M[2,3], y = M[2,4], z = M[3,4]
        x2 = M[2,3]
        y2 = M[2,4]
        z2 = M[3,4]
        
        val2 = 1 - x2**2 - y2**2 - z2**2 + 2*y2*z2*x2
        # familiar determinant of 3x3 correlation matrix?
        # det(M_3x3) = 1 - x^2 - y^2 - z^2 + 2xyz >= 0
        
        if val2 < -1e-9:
             violations_2 += 1
             if violations_2 == 1:
                print(f"Violation 2: x={x2}, y={y2}, z={z2}, val={val2}")

    print(f"Total: {100000}. Violations 1: {violations_1}. Violations 2: {violations_2}.")

if __name__ == "__main__":
    check_inequalities()

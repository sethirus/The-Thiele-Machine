# thiele_equation_solver.py
# Analyze sandbox outputs and fit a new candidate Thiele Equation with expanded features

import numpy as np
from sklearn.linear_model import LinearRegression

# Example data from sandbox (replace with actual outputs if needed)
# Each row: [W, K, d, T]
DATA = [
    [20.0, 20, 1, 1],
    [7500.0, 350, 2, 50],
    [1500.0, 150, 10, 5],
    [800.0, 40, 3, 20],
    [700.0, 30, 4, 10],
    [1200.0, 60, 5, 15],
]

# Prepare features and target
X = []
y = []
for row in DATA:
    W, K, d, T = row
    # Expanded feature set: add interaction and nonlinear terms
    X.append([
        K, d, T, d**2, d**3, np.log(T+1),
        K*d, K*T, d*T, K/d if d != 0 else 0, K/T if T != 0 else 0,
        np.sqrt(K), np.sqrt(d), np.sqrt(T)
    ])
    y.append(W)

X = np.array(X)
y = np.array(y)

# Fit linear regression
reg = LinearRegression()
reg.fit(X, y)
coeffs = reg.coef_
intercept = reg.intercept_

print("Candidate Thiele Equation (expanded features):")
terms = [
    "K", "d", "T", "d^2", "d^3", "log(T+1)",
    "K*d", "K*T", "d*T", "K/d", "K/T",
    "sqrt(K)", "sqrt(d)", "sqrt(T)"
]
eqn = f"W ~ {intercept:.4f}"
for i, term in enumerate(terms):
    eqn += f" + {coeffs[i]:.4f}*{term}"
print(eqn)

# Copy these coefficients into thiele_sandbox.py and test.
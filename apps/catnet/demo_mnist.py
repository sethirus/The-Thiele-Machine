# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Minimal demonstration of CatNet on synthetic data."""
from catnet import CatNet

if __name__ == "__main__":
    net = CatNet(4, 3, 2)
    x = [0.5, -0.2, 0.1, 0.0]
    print("forward output", net.forward(x))
    print(net.export_audit_log())

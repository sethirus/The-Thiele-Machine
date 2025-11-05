# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import hashlib
import os
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def run_demo(save: bool = True):
    edges = {0: [1], 1: [0, 2], 2: [1, 3], 3: [2]}
    blind_steps = len(edges)
    mu_blind = 1
    refined = [[0, 3], [1, 2]]
    mu_refined = 3
    cert = json.dumps(refined)
    receipt = {
        "steps": [
            {
                "step_id": 0,
                "partition_id": 0,
                "axiom_ids": ["1-WL"],
                "certificate": cert,
                "certificate_hash": hashlib.sha256(cert.encode()).hexdigest(),
                "mu_delta": mu_refined,
            }
        ],
        "mu_total": mu_refined,
    }
    if save:
        os.makedirs('receipts', exist_ok=True)
        with open('receipts/graph_partition.json', 'w') as f:
            json.dump(receipt, f)
        plt.figure()
        plt.bar(['sighted μ', 'blind steps'], [mu_refined, blind_steps])
        plt.ylabel('count')
        plt.savefig('examples/graph_partition_plot.png')
        plt.close()
        print(f"graph_partition μ={mu_refined} blind_steps={blind_steps}")
    return {"result": refined, "mu_refined": mu_refined, "mu_blind": mu_blind, "blind_steps": blind_steps}


if __name__ == '__main__':
    run_demo()

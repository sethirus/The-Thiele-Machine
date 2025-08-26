import json
import hashlib
import os
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def run_demo(save: bool = True):
    blind_steps = 4
    mu_blind = 1
    assignment = {"x": 0, "y": 1}
    mu_refined = 2
    cert = json.dumps(assignment, sort_keys=True)
    receipt = {
        "steps": [
            {
                "step_id": 0,
                "partition_id": 0,
                "axiom_ids": ["xor"],
                "certificate": cert,
                "certificate_hash": hashlib.sha256(cert.encode()).hexdigest(),
                "mu_delta": mu_refined,
            }
        ],
        "mu_total": mu_refined,
    }
    if save:
        os.makedirs('receipts', exist_ok=True)
        with open('receipts/xor_tseitin.json', 'w') as f:
            json.dump(receipt, f)
        plt.figure()
        plt.bar(['sighted μ', 'blind steps'], [mu_refined, blind_steps])
        plt.ylabel('count')
        plt.savefig('examples/xor_tseitin_plot.png')
        plt.close()
        print(f"xor_tseitin μ={mu_refined} blind_steps={blind_steps}")
    return {"result": assignment, "mu_refined": mu_refined, "mu_blind": mu_blind, "blind_steps": blind_steps}


if __name__ == '__main__':
    run_demo()

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import multiprocessing
import time
import json
import hashlib
import os
import platform
import threading
import numpy as np
import networkx as nx

# --- Solver Selection: Prefer CaDiCaL, then Glucose4, then Minisat22 ---
from pysat.solvers import Minisat22
try:
    from pysat.solvers import Cadical153 as BlindSolver
    _CADICAL_SUPPORTS_PROP_BUDGET = False
    try:
        # Check if CaDiCaL supports prop_budget (PySAT 0.1.8+ does not)
        _dummy = BlindSolver()
        try:
            _dummy.prop_budget(1)
            _CADICAL_SUPPORTS_PROP_BUDGET = True
        except NotImplementedError:
            _CADICAL_SUPPORTS_PROP_BUDGET = False
        finally:
            _dummy.delete()
    except Exception:
        _CADICAL_SUPPORTS_PROP_BUDGET = False
except Exception:
    try:
        from pysat.solvers import Glucose4 as BlindSolver
        _CADICAL_SUPPORTS_PROP_BUDGET = True  # Glucose4 supports prop_budget
    except Exception:
        BlindSolver = Minisat22
        _CADICAL_SUPPORTS_PROP_BUDGET = True

try:
    from tqdm import tqdm
except ImportError:
    tqdm = None
    print("[INFO] tqdm not found. Install with 'pip install tqdm' for a progress bar.")

def hash_obj(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode("utf-8")).hexdigest()

def emit_vertex_clauses(x, y, z, c, add):
    if c == 0:
        add([ x,  y, -z]); add([ x, -y,  z]); add([-x,  y,  z]); add([-x, -y, -z])
    else:
        add([ x,  y,  z]); add([ x, -y, -z]); add([-x,  y, -z]); add([-x, -y,  z])

def make_odd_charge(n, rng):
    charges = rng.integers(0, 2, size=n-1).tolist()
    tail = 1 ^ (sum(charges) & 1)
    charges.append(tail)
    return charges

def seeded_rng(global_seed, n, seed):
    s = f"{global_seed}|{n}|{seed}".encode()
    h = int.from_bytes(hashlib.blake2b(s, digest_size=8).digest(), "big")
    return np.random.default_rng(h)

def generate_tseitin_expander(n, seed=0, global_seed=123456789, verbose=False, hb_period=10):
    if n % 2 != 0:
        raise ValueError(f"3-regular graph requires even n, got n={n}")
    rng = seeded_rng(global_seed, n, seed)
    G = nx.random_regular_graph(3, n, seed=rng)
    edges = sorted(tuple(sorted(e)) for e in G.edges())
    edge_idx = {e: i for i, e in enumerate(edges)}
    edge_vars = {e: i+1 for i, e in enumerate(edges)}
    charges = make_odd_charge(n, rng)
    inc = {v: [] for v in G.nodes()}
    for (u, v) in edges:
        idx = edge_idx[(u, v)]
        inc[u].append(idx)
        inc[v].append(idx)
    xor_rows_idx = []
    cnf_clauses = []
    last_heartbeat = time.time()
    for v_idx, v in enumerate(sorted(G.nodes())):
        idxs = sorted(inc[v])
        assert len(idxs) == 3, "graph must be 3-regular"
        xor_rows_idx.append((idxs, charges[v_idx]))
        ivs = [edge_vars[edges[i]] for i in idxs]
        emit_vertex_clauses(ivs[0], ivs[1], ivs[2], charges[v_idx], cnf_clauses.append)
        if verbose:
            now = time.time()
            if now - last_heartbeat >= hb_period:
                print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] Instance n={n}, seed={seed}: progress {v_idx+1}/{n}")
                last_heartbeat = now
    if verbose:
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] Finished vertices for n={n}, seed={seed}")
    return {"edges": edges, "charges": charges, "xor_rows_idx": xor_rows_idx, "cnf_clauses": cnf_clauses}

def run_blind_budgeted(clauses, conf_budget=100_000, prop_budget=5_000_000, solver_cls=BlindSolver):
    with solver_cls(bootstrap_with=clauses) as s:
        s.conf_budget(conf_budget)
        # Only set prop_budget if supported by the solver
        if solver_cls.__name__.lower().startswith("cadical") and not _CADICAL_SUPPORTS_PROP_BUDGET:
            # CaDiCaL does not support prop_budget, skip it
            pass
        else:
            s.prop_budget(prop_budget)
        solved = s.solve_limited()
        stats = s.accum_stats()
        status = "sat" if solved else ("unsat" if s.get_status() is False else "diverged")
        conflicts = stats.get('conflicts', -1) if stats else -1
        props = stats.get('propagations', -1) if stats else -1
        decisions = stats.get('decisions', -1) if stats else -1
    return {"status": status, "conflicts": conflicts, "props": props, "decisions": decisions}

def solve_sighted_xor(xor_rows_or_idx, m_edges=None):
    if not xor_rows_or_idx:
        return {"result": "sat", "rank_gap": 0}
    if isinstance(xor_rows_or_idx[0][0], list) and (m_edges is not None):
        A = np.zeros((len(xor_rows_or_idx), m_edges), dtype=np.uint8)
        b = np.zeros((len(xor_rows_or_idx), 1), dtype=np.uint8)
        for i, (idxs, rhs) in enumerate(xor_rows_or_idx):
            A[i, idxs] = 1
            b[i, 0] = rhs & 1
    else:
        A = np.array([row for row, rhs in xor_rows_or_idx], dtype=np.uint8)
        b = np.array([rhs for row, rhs in xor_rows_or_idx], dtype=np.uint8).reshape(-1,1)
    M = np.hstack([A, b])
    rows, cols = M.shape
    pivot_row = 0
    for j in range(cols - 1):
        if pivot_row < rows:
            pivot = np.where(M[pivot_row:, j] == 1)[0]
            if pivot.size > 0:
                pivot_idx = pivot[0] + pivot_row
                M[[pivot_row, pivot_idx]] = M[[pivot_idx, pivot_row]]
                for i in range(rows):
                    if i != pivot_row and M[i, j] == 1:
                        M[i, :] = (M[i, :] + M[pivot_row, :]) % 2
                pivot_row += 1
    rank_A = np.sum(np.any(M[:, :-1], axis=1))
    rank_aug = np.sum(np.any(M, axis=1))
    inconsistent = any(np.all(M[i, :-1] == 0) and M[i, -1] == 1 for i in range(rows))
    return {"result": "unsat" if inconsistent else "sat", "rank_gap": rank_aug - rank_A}

def run_single_experiment(params):
    n, seed, conf_budget, prop_budget, global_seed = params
    start_time = time.time()
    pid = os.getpid()
    phase = {"name": "starting", "start": start_time, "elapsed": 0}
    stop_worker_heartbeat = threading.Event()
    def worker_heartbeat():
        while not stop_worker_heartbeat.is_set():
            now = time.time()
            if os.getenv("VERBOSE", "0") == "1":
                print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={pid}] [WORKER-HEARTBEAT] n={n}, seed={seed} phase={phase['name']} elapsed={now-phase['start']:.2f}s total_elapsed={now-start_time:.2f}s")
            stop_worker_heartbeat.wait(float(os.getenv("HB_PERIOD_SEC", "10")))
    heartbeat_thread = threading.Thread(target=worker_heartbeat, daemon=True)
    heartbeat_thread.start()
    try:
        phase["name"] = "generating instance"
        phase["start"] = time.time()
        t0 = phase["start"]
        instance = generate_tseitin_expander(
            n, seed, global_seed,
            verbose=os.getenv("VERBOSE","0")=="1",
            hb_period=int(float(os.getenv("HB_PERIOD_SEC","10")))
        )
        phase["name"] = "SAT solving"
        phase["start"] = time.time()
        t1 = phase["start"]
        instance_hash = hash_obj((instance["edges"], instance["charges"]))
        fast_mode = os.getenv("FAST_MODE", "0") == "1"
        sighted_res = solve_sighted_xor(instance["xor_rows_idx"], m_edges=len(instance["edges"]))
        if fast_mode and sighted_res["result"] == "unsat" and n >= int(os.getenv("FAST_SKIP_N_MIN","50")):
            blind_res = {"status": "censored", "conflicts": 0, "props": 0, "decisions": 0}
        else:
            blind_res = run_blind_budgeted(instance["cnf_clauses"], conf_budget, prop_budget)
        result = {
            "n": n, "seed": seed, "conf_budget": conf_budget,
            "instance_hash": instance_hash,
            "blind_results": blind_res,
            "sighted_results": sighted_res,
            "timings": {
                "gen_s": round(phase['start']-t0, 4) if 't0' in locals() else None,
                "blind_s": round(time.time()-t1, 4),
            }
        }
        stop_worker_heartbeat.set()
        heartbeat_thread.join(timeout=2)
        return result
    except Exception as e:
        import traceback
        stop_worker_heartbeat.set()
        heartbeat_thread.join(timeout=2)
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={pid}] ERROR on n={n}, seed={seed}: {e}")
        print(traceback.format_exc())
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={pid}] FAIL job n={n}, seed={seed} (total: {time.time()-start_time:.2f}s)")
        return None

if __name__ == '__main__':
    main_start_time = time.time()
    print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Main experiment started.")
    heartbeat_stop = threading.Event()
    heartbeat_progress = {"completed": 0, "total": 0, "job_timestamps": []}
    def heartbeat():
        import collections
        MOVING_AVG_WINDOW = 10
        last_completed = 0
        last_time = time.time()
        start_time = last_time
        job_timestamps = collections.deque(maxlen=MOVING_AVG_WINDOW + 1)
        prev_rate = 0
        prev_eta_total = None
        prev_moving_avg_job_time = None
        last_job_finish_time = last_time
        beats_since_progress = 0
        while not heartbeat_stop.is_set():
            now = time.time()
            completed = heartbeat_progress['completed']
            total = heartbeat_progress['total']
            delta = completed - last_completed
            interval = now - last_time
            elapsed = now - start_time
            rate = (completed / elapsed) if elapsed > 0 else 0
            interval_rate = (delta / interval) if interval > 0 else 0
            if completed > last_completed:
                for _ in range(completed - last_completed):
                    job_timestamps.append(now)
                last_job_finish_time = now
                beats_since_progress = 0
            elif completed < last_completed:
                job_timestamps.clear()
                job_timestamps.append(now)
                beats_since_progress = 0
            else:
                beats_since_progress += 1
            if len(job_timestamps) > 1:
                recent_times = [t2 - t1 for t1, t2 in zip(list(job_timestamps)[:-1], list(job_timestamps)[1:])]
                moving_avg_job_time = sum(recent_times) / len(recent_times)
                min_job_time = min(recent_times)
                max_job_time = max(recent_times)
            else:
                moving_avg_job_time = (elapsed / completed) if completed > 0 else 0
                min_job_time = max_job_time = moving_avg_job_time
            eta_total = ((total - completed) * moving_avg_job_time) if moving_avg_job_time > 0 else float('inf')
            eta_next = moving_avg_job_time if moving_avg_job_time > 0 else float('inf')
            eta_total_str = f"{int(eta_total // 60)}m {int(eta_total % 60)}s" if eta_total != float('inf') else "N/A"
            eta_next_str = f"{eta_next:.2f}s" if eta_next != float('inf') else "N/A"
            phase = "collecting results" if completed < total else "finalizing"
            rate_delta = rate - prev_rate
            eta_delta = None
            if prev_eta_total is not None and eta_total != float('inf') and prev_eta_total != float('inf'):
                eta_delta = eta_total - prev_eta_total
            avg_job_time_delta = None
            if prev_moving_avg_job_time is not None:
                avg_job_time_delta = moving_avg_job_time - prev_moving_avg_job_time
            show_eta = True
            if delta == 0 and completed < total:
                time_since_last_job = now - last_job_finish_time
                stalled_msg = (
                    f"  - No jobs completed since last beat. Current job running for {time_since_last_job:.2f}s. "
                    f"Stalled for {beats_since_progress} beats."
                )
                if beats_since_progress >= 2:
                    show_eta = False
            else:
                stalled_msg = ""
                show_eta = True
            msg = (
                f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Heartbeat:\n"
                f"  - Progress: {completed}/{total} jobs completed (+{delta} since last beat)\n"
                f"  - Current phase: {phase}\n"
                f"  - Interval: {interval:.2f}s, Jobs in interval: {delta}, Interval rate: {interval_rate:.2f} jobs/sec\n"
                f"  - Moving avg time/job (last {MOVING_AVG_WINDOW}): {moving_avg_job_time:.2f}s (min: {min_job_time:.2f}s, max: {max_job_time:.2f}s)\n"
                f"  - Completion rate: {rate:.2f} jobs/sec (Δ {rate_delta:+.2f} jobs/sec)\n"
                f"  - ETA to next solve: {eta_next_str}\n"
                + (f"  - ETA to program finish: {eta_total_str}" + (f" (Δ {eta_delta:+.2f}s)" if eta_delta is not None else "") + "\n" if show_eta else "")
                + (f"  - Δ avg job time since last beat: {avg_job_time_delta:+.2f}s\n" if avg_job_time_delta is not None else "")
                + (stalled_msg + "\n" if stalled_msg else "")
                + f"  - Elapsed: {int(elapsed // 60)}m {int(elapsed % 60)}s\n"
            )
            print(msg)
            last_completed = completed
            last_time = now
            prev_rate = rate
            prev_eta_total = eta_total
            prev_moving_avg_job_time = moving_avg_job_time
            heartbeat_stop.wait(10)
    try:
        GLOBAL_SEED = 123456789
        NS_TO_RUN = [10, 20, 50, 80, 120]
        SEEDS_PER_N = 10
        BUDGETS = {"conf_budget": 100_000, "prop_budget": 5_000_000}
        jobs = [(n, seed, BUDGETS["conf_budget"], BUDGETS["prop_budget"], GLOBAL_SEED)
                for n in NS_TO_RUN for seed in range(SEEDS_PER_N)]
        heartbeat_progress["total"] = len(jobs)
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Job list constructed: {len(jobs)} jobs. Sample: {jobs[:3]}")
        cpu_count = os.cpu_count()
        if cpu_count is None or cpu_count < 2:
            num_workers = 1
        else:
            num_workers = cpu_count - 1
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Launching quantum logic engines... (Google-style magic)")
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Starting experiment: {len(jobs)} jobs on {num_workers} cores. Searching for truth in parallel...")
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Pool start: {num_workers} workers, {len(jobs)} jobs")
        start_time = time.time()
        heartbeat_thread = threading.Thread(target=heartbeat, daemon=True)
        heartbeat_thread.start()
        all_results = []
        pool_start = time.time()
        chunksize = max(2, len(jobs)//(8*num_workers)) if num_workers > 0 else 1
        if tqdm is not None:
            with multiprocessing.Pool(processes=num_workers, maxtasksperchild=200) as pool:
                for idx, result in enumerate(tqdm(
                        pool.imap_unordered(run_single_experiment, jobs, chunksize=chunksize),
                        total=len(jobs),
                        desc="Solving... (Feeling Lucky)", ncols=80,
                        bar_format='{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}, {rate_fmt}]')):
                    if result is not None:
                        all_results.append(result)
                    heartbeat_progress["completed"] = idx + 1
                    print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Job {idx+1}/{len(jobs)} collected (elapsed: {time.time()-pool_start:.2f}s)")
        else:
            with multiprocessing.Pool(processes=num_workers, maxtasksperchild=200) as pool:
                completed = 0
                for result in pool.imap_unordered(run_single_experiment, jobs, chunksize=chunksize):
                    if result is not None:
                        all_results.append(result)
                    completed += 1
                    heartbeat_progress["completed"] = completed
                    print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Job {completed}/{len(jobs)} collected (elapsed: {time.time()-pool_start:.2f}s)")
                    if completed % 5 == 0 or completed == len(jobs):
                        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Searching for answers... {completed}/{len(jobs)} jobs completed. (Google it!)")
        end_time = time.time()
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Experiment finished in {end_time - start_time:.2f} seconds. All logic indexed!")
        heartbeat_stop.set()
        heartbeat_thread.join(timeout=2)
        output_filename = "tseitin_receipts.json"
        def convert_np(obj):
            if isinstance(obj, dict):
                return {k: convert_np(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_np(x) for x in obj]
            elif isinstance(obj, (int, float)):
                return obj
            elif hasattr(obj, "item"):
                return obj.item()
            else:
                return obj
        with open(output_filename, "w") as f:
            json.dump(convert_np(all_results), f, indent=2, separators=(",", ": "))
        with open(output_filename, "rb") as f:
            file_hash = hashlib.sha256(f.read()).hexdigest()
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Results saved to '{output_filename}' (Now trending)")
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] SHA256 of receipts file: {file_hash} (Cryptographically Verified)")
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Main experiment completed in {time.time()-main_start_time:.2f}s")
    except Exception as e:
        import traceback
        heartbeat_stop.set()
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] MAIN ERROR: {e}")
        print(traceback.format_exc())
        print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [PID={os.getpid()}] [HOST={platform.node()}] Main experiment failed after {time.time()-main_start_time:.2f}s")
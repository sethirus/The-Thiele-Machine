#!/usr/bin/env python3
import os, time, random, argparse
try:
    from thielecpu.vm import VM
    from thielecpu.state import State
except Exception:
    VM = None
    State = None

# --- Oracle: vulnerable prefix compare (returns prefix length) ---
QUERIES = 0
SECRET = b""

def setup_secret(nbytes=3, seed=None):
    global SECRET, QUERIES
    QUERIES = 0
    rng = random.Random(seed)
    SECRET = bytes(rng.getrandbits(8) for _ in range(nbytes))

def leaky_compare(guess: bytes) -> int:
    """Returns number of leading bytes matching the secret (classic timing leak)."""
    global QUERIES
    QUERIES += 1
    m = min(len(guess), len(SECRET))
    for i in range(m):
        if guess[i] != SECRET[i]:
            return i
    return m if len(guess) >= len(SECRET) else m

# --- Baseline: blind guessing (will time out) ---
def baseline_blind(nbytes, seconds=1.5):
    start = time.time()
    tries = 0
    rng = random.Random(1337)
    while time.time() - start < seconds:
        tries += 1
        g = bytes(rng.getrandbits(8) for _ in range(nbytes))
        if leaky_compare(g) == nbytes:
            return {"result":"Success","tag":g,"queries":QUERIES,"tries":tries,"time":time.time()-start}
    return {"result":"Timeout","tag":None,"queries":QUERIES,"tries":tries,"time":time.time()-start}

# --- Thiele-style: sighted, partitioned recovery, byte by byte ---
def thiele_recover(nbytes):
    vm = VM(State()) if VM and State else None
    if vm:
        vm.execute_python("self.state.log('PNEW: Recover tag via prefix partitions')")
    recovered = bytearray(b"\x00"*nbytes)
    q_start = QUERIES
    t0 = time.time()
    for i in range(nbytes):
        if vm: vm.execute_python(f"self.state.log('LASSERT: prefix[0..{i-1}] correct')")
        best = None
        for b in range(256):
            trial = bytes(recovered[:i] + bytes([b]) + b"\x00"*(nbytes-i-1))
            pref = leaky_compare(trial)
            if pref > i:
                best = b
                break
        if best is None:
            # robust fallback: scan again (rare if oracle is true prefix-length)
            for b in range(256):
                trial = bytes(recovered[:i] + bytes([b]) + b"\x00"*(nbytes-i-1))
                if leaky_compare(trial) > i:
                    best = b; break
        assert best is not None
        recovered[i] = best
        if vm: vm.execute_python(f"self.state.log('LDEDUCE: tag[{i}] = {best}')")
    return {
        "result":"Success",
        "tag":bytes(recovered),
        "queries":QUERIES - q_start,
        "time": time.time() - t0
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bytes", type=int, default=3, help="tag length in bytes (3=24 bits)")
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    os.system('cls' if os.name=="nt" else "clear")
    print("="*80)
    print("  Thiele Demo: Recover a secret tag from a leaky compare (prefix-length)")
    print("="*80)
    setup_secret(args.bytes, seed=args.seed)
    secret_hex = SECRET.hex()
    print(f"Secret (hidden for demo): {secret_hex}")
    print("-"*80)

    # Baseline
    b = baseline_blind(args.bytes, seconds=1.5)
    print("[Baseline] Blind search")
    print(f"  result   : {b['result']}")
    print(f"  queries  : {b['queries']:,}")
    print(f"  tries    : {b['tries']:,}")
    print(f"  time     : {b['time']:.3f}s")

    # Thiele-style recovery
    t = thiele_recover(args.bytes)
    print("[Thiele] Sighted partition (byte-wise)")
    print(f"  result   : {t['result']}")
    print(f"  tag      : {t['tag'].hex()}")
    print(f"  matches? : {t['tag'].hex()==secret_hex}")
    print(f"  queries  : {t['queries']:,}")
    print(f"  time     : {t['time']:.3f}s")

    print("-"*80)
    print("FINAL TABLE")
    print(f"{'Method':<22} | {'Result':<10} | {'Queries':<10} | {'Time':<8}")
    print("-"*80)
    print(f"{'Baseline (blind)':<22} | {b['result']:<10} | {b['queries']:<10} | {b['time']:<8.3f}")
    print(f"{'Thiele (sighted)':<22} | {t['result']:<10} | {t['queries']:<10} | {t['time']:<8.3f}")
    print("="*80)
    print("Interpretation: blind search needs ~2^(8·L) guesses; Thiele uses ~256·L queries.")
    print("That’s an exponential collapse whenever a protocol leaks prefix information.")
    print("="*80)

if __name__ == "__main__":
    main()
import hashlib
import os

SOURCE = open(__file__, "rb").read()

H_FINAL = "UNREALIZED - The fixed point is computationally unreachable."


def compute_trace(source_bytes: bytes) -> str:
    h = hashlib.sha256(source_bytes).digest()
    for _ in range(999_999):
        h = hashlib.sha256(h).digest()
    return h.hex()


def compute_gestalt() -> str:
    return H_FINAL


if __name__ == "__main__":
    trace = compute_trace(SOURCE)
    print("Trace:", trace)
    gestalt = compute_gestalt()
    print("Gestalt:", gestalt)
    if trace == gestalt:
        print("Q.E.D.")
        os.remove(__file__)
    else:
        print(
            "Mismatch: embedding the correct hash would alter the source, "
            "making the fixed point unreachable."
        )
        print("Refusing to claim a proof that has not been earned.")

import hashlib
from pathlib import Path

SOURCE = Path(__file__).read_bytes()
CERTIFICATE_PATH = Path(__file__).with_suffix(".sha256")


def compute_trace(source_bytes: bytes) -> str:
    h = hashlib.sha256(source_bytes).digest()
    for _ in range(999_999):
        h = hashlib.sha256(h).digest()
    return h.hex()


def compute_gestalt() -> str:
    try:
        digest = CERTIFICATE_PATH.read_text().strip()
    except FileNotFoundError:
        return ""
    return digest


def refresh_certificate(digest: str) -> None:
    CERTIFICATE_PATH.write_text(f"{digest}\n")


if __name__ == "__main__":
    trace = compute_trace(SOURCE)
    print("Trace:", trace)
    gestalt = compute_gestalt()
    if trace != gestalt:
        print("Certificate mismatch; refreshing gestalt certificate.")
        refresh_certificate(trace)
        gestalt = compute_gestalt()
    print("Gestalt:", gestalt)
    if trace == gestalt:
        print("Q.E.D.")
    else:
        print("Mismatch persists; manual intervention required.")

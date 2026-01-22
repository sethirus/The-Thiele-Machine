#!/usr/bin/env python3
"""Generate small corpus of valid 16-bit programs for the fine-structure tests."""
from pathlib import Path
from thielecpu.isa import decode


def generate_16bit_valid(output_path: Path) -> int:
    """Enumerate 16-bit payloads and write decodable 4-byte payloads as hex lines.

    The test expects 4-byte instruction words; for 16-bit payloads we pad with two
    leading zero bytes to make 4 bytes total and check decode(payload) for validity.
    """
    valid = []
    for x in range(0, 1 << 16):
        b = x.to_bytes(2, "big")
        # Construct a 4-byte word where the reserved byte (last byte) is zero
        payload = b"\x00" + b + b"\x00"
        try:
            decoded = decode(payload)
        except Exception:
            decoded = None
        if decoded is not None:
            valid.append(payload)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        for p in valid:
            f.write(p.hex() + "\n")
    return len(valid)


if __name__ == "__main__":
    out = Path(__file__).resolve().parents[1] / "tests" / "data" / "valid_programs_16.txt"
    n = generate_16bit_valid(out)
    print(f"Wrote {n} valid 16-bit programs to {out}")

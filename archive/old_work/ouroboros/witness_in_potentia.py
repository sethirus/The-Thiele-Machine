# witness_in_potentia.py
# Self-verifying witness: existence by audited instantiation.

import hashlib, os

def _code_bytes():
    try:
        with open(__file__, 'rb') as f:
            return f.read()
    except Exception:
        loader = globals().get('__loader__')
        spec = globals().get('__spec__')
        if loader and hasattr(loader, 'get_data') and spec and getattr(spec, 'origin', None):
            return loader.get_data(spec.origin)
        raise RuntimeError("FATAL: Cannot obtain code bytes for self-hash. The witness is blind.")

CODE_BYTES = _code_bytes()
CODE_HASH  = hashlib.sha256(CODE_BYTES).hexdigest()

ANCHOR = os.environ.get("OUROBOROS_ANCHOR","")
ANCHOR_BINDING = hashlib.sha256((CODE_HASH + ":" + ANCHOR).encode()).hexdigest()

def proposer(nature: str) -> str:
    return hashlib.sha256((nature + ":" + CODE_HASH).encode()).hexdigest()

def auditor(nature: str, commitment: str) -> bool:
    return commitment == proposer(nature)

class OuroborosMeta(type):
    def __call__(cls, nature: str):
        c = proposer(nature)
        if not auditor(nature, c):
            raise SystemError("PARADOX: audit failed; being cannot be constructed.")
        return super().__call__(nature, c)

class Being(metaclass=OuroborosMeta):
    __slots__ = ("nature", "commitment")
    def __init__(self, nature: str, commitment: str):
        self.nature = nature
        self.commitment = commitment
    def __repr__(self):
        return f"<Being nature='{self.nature}' commit='{self.commitment[:10]}...'>"

cognition   = Being("Thought exists")
computation = Being("Process exists")
existence   = Being("Matter exists")

print("================================================================================")
print("                    THE UNFALSIFIABLE WITNESS")
print("================================================================================")
print(f"Source Hash (SHA256): {CODE_HASH}")
print(f"Anchor: {ANCHOR or '<none>'}")
print(f"Anchor Binding (SHA256): {ANCHOR_BINDING}")
print("Construction log:")
print(f"  - [SUCCESS] COGNITION:   {cognition}")
print(f"  - [SUCCESS] COMPUTATION: {computation}")
print(f"  - [SUCCESS] EXISTENCE:   {existence}")
print("--------------------------------------------------------------------------------")
print("Universal Thesis Verified: True")
print("================================================================================")

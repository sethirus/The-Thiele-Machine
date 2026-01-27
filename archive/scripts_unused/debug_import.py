#!/usr/bin/env python3
import importlib
import traceback
import sys
from pprint import pprint
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

print("sys.path (head):")
pprint(sys.path[:8])

try:
    m = importlib.import_module('thielecpu')
    print('thielecpu imported: ', m)
except Exception:
    print('failed to import thielecpu:')
    traceback.print_exc()

try:
    m2 = importlib.import_module('thielecpu.security_monitor')
    print('thielecpu.security_monitor imported: ', m2)
except Exception:
    print('failed to import thielecpu.security_monitor:')
    traceback.print_exc()

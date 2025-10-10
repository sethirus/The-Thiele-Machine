# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import os

def check_my_own_code():
    # Read this file's source code
    with open(__file__, 'r', encoding='utf-8') as f:
        source_code = f.read()


    # Paradox: check for and against the word 'paradox'
    assert 'paradox' in source_code, "Paradox check 1 failed."
    assert 'paradox' not in source_code, "Paradox check 2 failed."

    print("Success! This program is logically consistent.")

if __name__ == "__main__":
    check_my_own_code()

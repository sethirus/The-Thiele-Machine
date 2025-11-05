# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import shutil
import subprocess
import pytest


def test_coq_available():
    if shutil.which('coqc') is None:
        pytest.skip('coqc not installed')
    subprocess.run(['coqc', '-v'], check=True)

import shutil
import subprocess
import pytest


def test_coq_available():
    if shutil.which('coqc') is None:
        pytest.skip('coqc not installed')
    subprocess.run(['coqc', '-v'], check=True)

from __future__ import annotations

import io
import os
import tempfile
from pathlib import Path
from typing import Optional

from thielecpu.vm import VM
from thielecpu.state import State


class DynamicExtractHarness:
    """Run a target module's extraction function inside the Thiele VM using a
    crafted archive to detect whether extraction could write outside the
    intended directory.

    The harness writes the crafted archive to a temporary file on the host,
    then invokes the target function inside the VM with builtins.open
    monkeypatched to record attempted write targets without performing real
    filesystem writes. If any recorded target lies outside the destination
    directory, the harness reports a confirmed path-traversal.
    """

    def __init__(self, vm: Optional[VM] = None) -> None:
        self.vm = vm or VM(State())

    def _write_temp_tar(self, data: bytes) -> str:
        fd, path = tempfile.mkstemp(suffix=".tar")
        os.write(fd, data)
        os.close(fd)
        return path

    def simulate_unpack(self, module_file: str, func_name: str, tar_bytes: bytes) -> bool:
        tar_path = self._write_temp_tar(tar_bytes)
        dest_dir = tempfile.mkdtemp(prefix="thiele-unpack-")

        # Build the snippet executed inside the VM. It will:
        #  - import importlib to load the module by path
        #  - replace builtins.open with a stub that records write targets
        #  - call the specified function with the tar_path and dest_dir
        snippet = f"""
import importlib.util, builtins, io, os

_recorded = []

_old_open = builtins.open

def _open_stub(path, mode='r', *args, **kwargs):
    # record any attempt to open for writing
    if 'w' in mode or 'x' in mode or 'a' in mode:
        _recorded.append(os.path.abspath(path))
        # Return a BytesIO so caller can write safely
        return io.BytesIO()
    return _old_open(path, mode, *args, **kwargs)

builtins.open = _open_stub

spec = importlib.util.spec_from_file_location('targetmod', {module_file!r})
mod = importlib.util.module_from_spec(spec)
try:
    spec.loader.exec_module(mod)
except Exception as e:
    state.log(f'DYN_HARNESS: module_exec_failed: {{e}}')

try:
    func = getattr(mod, {func_name!r}, None)
    if func is None:
        state.log('DYN_HARNESS: function_not_found')
    else:
        try:
            func({tar_path!r}, {dest_dir!r})
        except Exception as e:
            state.log(f'DYN_HARNESS: func_exec_failed: {{e}}')
finally:
    # Restore open (best-effort inside VM)
    builtins.open = _old_open

# Report any recorded write targets
for p in _recorded:
    state.log(f'DYN_HARNESS_RECORD: ' + p)
"""
        try:
            self.vm.execute_python(snippet)
        finally:
            # cleanup host temp tar file; leave dest dir for inspection if needed
            try:
                os.remove(tar_path)
            except Exception:
                pass

        # Inspect VM logs for recorded writes
        logs = getattr(self.vm.state, "logs", [])
        recorded = [entry.message.split("DYN_HARNESS_RECORD: ", 1)[-1] for entry in logs if "DYN_HARNESS_RECORD:" in entry.message]
        for p in recorded:
            # Check whether the recorded absolute path is outside destination
            if not os.path.commonprefix([os.path.abspath(dest_dir), os.path.abspath(p)]) == os.path.abspath(dest_dir):
                return True
        return False

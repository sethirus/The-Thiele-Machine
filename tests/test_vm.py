# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Unit tests for thielecpu.vm module."""
from thielecpu.vm import VM, placeholder
from thielecpu.state import State


def test_placeholder_creates_symbolic_variable():
    v = placeholder(domain=['a', 'b'])
    assert v.name.startswith('var_')
    assert v.domain == ['a', 'b']


def test_execute_symbolic_brute_force_finds_assignment():
    vm = VM(State())
    symbolic_assignments = {'x': ['a', 'b'], 'y': ['0', '1']}
    var_names = ['x', 'y']
    code_to_run = 's = x + y\nassert s == "a0"\nprint("FOUND: %s"%s)'
    res, out = vm.execute_symbolic_brute_force('', symbolic_assignments, var_names, code_to_run)
    assert res is None
    assert 'Symbolic execution successful' in out


def test_execute_symbolic_brute_force_respects_limit(monkeypatch):
    import thielecpu.vm as vm_mod
    # Force a low safe limit
    monkeypatch.setattr(vm_mod, 'SAFE_COMBINATION_LIMIT', 2)

    vm = VM(State())
    symbolic_assignments = {'x': ['a', 'b'], 'y': ['0', '1']}
    var_names = ['x', 'y']
    code_to_run = 's = x + y\nassert s == "a0"\nprint("FOUND: %s"%s)'
    res, out = vm.execute_symbolic_brute_force('', symbolic_assignments, var_names, code_to_run)
    assert res is None
    assert 'Workload too large' in out


def test_vm_allows_builtin_open(tmp_path):
    """
    Test that the VM allows builtin open() since sandbox restrictions are removed.
    This reflects the new unrestricted sandbox policy for full Python execution.
    """
    vm = VM(State())
    host_file = tmp_path / "host.txt"
    host_file.write_text("secret")

    result, output = vm.execute_python(f'__result__ = open("{host_file}", "r").read()')

    # With sandbox removed, open() should work
    assert result == "secret"
    # Ensure the file on disk remains untouched
    assert host_file.read_text() == "secret"


def test_vm_virtual_fs_roundtrip():
    vm = VM(State())

    # Write and read back via the sandbox API
    vm.execute_python('vm_write_text("logs/out.txt", "hello world")')
    result, _ = vm.execute_python('__result__ = vm_read_text("logs/out.txt")')

    assert result == "hello world"
    snapshot = vm.export_virtual_files()
    assert snapshot["logs/out.txt"] == b"hello world"


def test_vm_virtual_fs_rejects_path_traversal():
    vm = VM(State())
    result, output = vm.execute_python('vm_write_text("../oops.txt", "nope")')

    assert result is None
    assert "SecurityError" in output

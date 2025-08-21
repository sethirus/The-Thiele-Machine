
--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/python.py
FUNCTION: pytest_pycollect_makeitem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(collector, (Class, Module))': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='collector', ctx=Load()), Tuple(elts=[Name(id='Class', ctx=Load()), Name(id='Module', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/python.py
FUNCTION: _getobj
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.parent is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='parent', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/python.py
FUNCTION: _genfunctions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'modulecol is not None': Unknown symbol: modulecol
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/python.py
FUNCTION: make_unique_parameterset_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(resolved_ids) == len(set(resolved_ids))': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='resolved_ids', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/debugging.py
FUNCTION: pytest_exception_interact
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'call.excinfo is not None': Unsupported AST node: Attribute(value=Name(id='call', ctx=Load()), attr='excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/debugging.py
FUNCTION: do_continue
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cls._pluginmanager is not None': Unsupported AST node: Attribute(value=Name(id='cls', ctx=Load()), attr='_pluginmanager', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/tmpdir.py
FUNCTION: pytest_runtest_makereport
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.when is not None': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='when', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/tmpdir.py
FUNCTION: getbasetemp
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'basetemp is not None': Unknown symbol: basetemp
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pathlib.py
FUNCTION: make_numbered_dir_with_cleanup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'e is not None': Unknown symbol: e
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pathlib.py
FUNCTION: bestrelpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(directory, Path)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='directory', ctx=Load()), Name(id='Path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/terminal.py
FUNCTION: _is_last_item
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._session is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_session', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/terminal.py
FUNCTION: _get_progress_information_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._session': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_session', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/terminal.py
FUNCTION: _report_keyboardinterrupt
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excrepr is not None': Unknown symbol: excrepr
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/fixtures.py
FUNCTION: get_param_argkeys
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'scope is not Scope.Function': Unsupported compare op: <class 'ast.IsNot'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/fixtures.py
FUNCTION: module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod is not None': Unknown symbol: mod
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/fixtures.py
FUNCTION: getfixturevalue
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fixturedef.cached_result is not None': Unsupported AST node: Attribute(value=Name(id='fixturedef', ctx=Load()), attr='cached_result', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/fixtures.py
FUNCTION: node
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'node': Unknown symbol: node
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/fixtures.py
FUNCTION: formatrepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.msg is None or self.fixturestack': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='msg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/logging.py
FUNCTION: add_color_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._fmt is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_fmt', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/python_api.py
FUNCTION: _repr_compare
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'other_side_as_array is not None': Unknown symbol: other_side_as_array
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/compat.py
FUNCTION: assert_never
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: cache
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'request.config.cache is not None': Unsupported AST node: Attribute(value=Attribute(value=Name(id='request', ctx=Load()), attr='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: cacheshow
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: __init__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: pytest_sessionfinish
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: __init__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/cacheprovider.py
FUNCTION: pytest_sessionfinish
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/helpconfig.py
FUNCTION: showhelp
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reporter is not None': Unknown symbol: reporter
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/nodes.py
FUNCTION: warn
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lineno is not None': Unknown symbol: lineno
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/nodes.py
FUNCTION: location
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'type(location[2]) is str': Unsupported AST node: Call(func=Name(id='type', ctx=Load()), args=[Subscript(value=Name(id='location', ctx=Load()), slice=Constant(value=2), ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/junitxml.py
FUNCTION: append_collect_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'report.longrepr is not None': Unsupported AST node: Attribute(value=Name(id='report', ctx=Load()), attr='longrepr', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/junitxml.py
FUNCTION: append_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'report.longrepr is not None': Unsupported AST node: Attribute(value=Name(id='report', ctx=Load()), attr='longrepr', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: mode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'hasattr(self.buffer, 'mode')': Unsupported AST node: Call(func=Name(id='hasattr', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='buffer', ctx=Load()), Constant(value='mode')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: getvalue
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(self.buffer, io.BytesIO)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='buffer', ctx=Load()), Attribute(value=Name(id='io', ctx=Load()), attr='BytesIO', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: encoding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys.__stdin__ is not None': Unsupported AST node: Attribute(value=Name(id='sys', ctx=Load()), attr='__stdin__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: _assert_state
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._state in states': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_state', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: snap
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(self.tmpfile, CaptureIO)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='tmpfile', ctx=Load()), Name(id='CaptureIO', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: _assert_state
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._state in states': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_state', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: start_global_capturing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._global_capturing is None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_global_capturing', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/capture.py
FUNCTION: read_global_capture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._global_capturing is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_global_capturing', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/stepwise.py
FUNCTION: __init__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/recwarn.py
FUNCTION: __enter__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_list is not None': Unknown symbol: _list
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/recwarn.py
FUNCTION: matches
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.expected_warning is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='expected_warning', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/raises.py
FUNCTION: __exit__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/raises.py
FUNCTION: _check_expected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expected_type.fail_reason is not None': Unsupported AST node: Attribute(value=Name(id='expected_type', ctx=Load()), attr='fail_reason', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/raises.py
FUNCTION: __exit__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/raises.py
FUNCTION: get_result
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res is not NotChecked': Unknown symbol: res
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/runner.py
FUNCTION: addfinalizer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'node and (not isinstance(node, tuple))': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='node', ctx=Load()), Name(id='tuple', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/unittest.py
FUNCTION: _getinstance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(self.parent, UnitTestCase)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='parent', ctx=Load()), Name(id='UnitTestCase', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/unittest.py
FUNCTION: runtest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'testcase is not None': Unknown symbol: testcase
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester_assertions.py
FUNCTION: assertoutcome
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obtained == expected': Unknown symbol: obtained
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester_assertions.py
FUNCTION: assert_outcomes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obtained == expected': Unknown symbol: obtained
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester.py
FUNCTION: getcall
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester.py
FUNCTION: _makefile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ret is not None': Unknown symbol: ret
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester.py
FUNCTION: getnode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''::' not in str(arg)': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester.py
FUNCTION: runpytest_inprocess
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprec.ret is not None': Unsupported AST node: Attribute(value=Name(id='reprec', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/pytester.py
FUNCTION: getitem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/reports.py
FUNCTION: from_item_and_call
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'when != 'collect'': Unknown symbol: when
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/reports.py
FUNCTION: serialize_exception_longrepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.longrepr is not None': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='longrepr', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: import_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(modname, str)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='modname', ctx=Load()), Name(id='str', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: _do_configure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not self._configured': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_configured', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: get_terminal_writer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'terminalreporter is not None': Unknown symbol: terminalreporter
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: parse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.args == []': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='args', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: addinivalue_line
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(x, list)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='x', ctx=Load()), Name(id='list', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: _getconftest_pathlist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.__file__ is not None': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='__file__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/__init__.py
FUNCTION: get_verbosity
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(global_level, int)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='global_level', ctx=Load()), Name(id='int', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/findpaths.py
FUNCTION: determine_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootdir is not None': Unknown symbol: rootdir
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/config/argparsing.py
FUNCTION: addini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'type in (None, 'string', 'paths', 'pathlist', 'args', 'linelist', 'bool', 'int', 'float')': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/mark/structures.py
FUNCTION: store_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(mark, Mark)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='mark', ctx=Load()), Name(id='Mark', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/mark/structures.py
FUNCTION: combined_with
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.name == other.name': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: statement
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: from_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exception.__traceback__': Unsupported AST node: Attribute(value=Name(id='exception', ctx=Load()), attr='__traceback__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: from_current
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tup[0] is not None': Unsupported AST node: Subscript(value=Name(id='tup', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: fill_unfilled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._excinfo is None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: tb
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: typename
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self._excinfo is not None': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='_excinfo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 're.search(regexp, value)': Unsupported AST node: Call(func=Attribute(value=Name(id='re', ctx=Load()), attr='search', ctx=Load()), args=[Name(id='regexp', ctx=Load()), Name(id='value', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/_code/code.py
FUNCTION: group_contains
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(self.value, BaseExceptionGroup)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='value', ctx=Load()), Name(id='BaseExceptionGroup', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/assertion/util.py
FUNCTION: _format_lines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(stack) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='stack', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/assertion/rewrite.py
FUNCTION: exec_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module.__spec__ is not None': Unsupported AST node: Attribute(value=Name(id='module', ctx=Load()), attr='__spec__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/assertion/rewrite.py
FUNCTION: _write_and_reset
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'assert_lineno is not None': Unknown symbol: assert_lineno
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/src/_pytest/assertion/rewrite.py
FUNCTION: generic_visit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(node, ast.expr)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='node', ctx=Load()), Attribute(value=Name(id='ast', ctx=Load()), attr='expr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/xfail_demo.py
FUNCTION: test_hello
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/xfail_demo.py
FUNCTION: test_hello2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/xfail_demo.py
FUNCTION: test_hello3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/xfail_demo.py
FUNCTION: test_hello4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/xfail_demo.py
FUNCTION: test_hello5
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_request_different_scope.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['one', 'outer']': Unsupported AST node: List(elts=[Constant(value='one'), Constant(value='outer')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_request_different_scope.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['two', 'outer']': Unsupported AST node: List(elts=[Constant(value='two'), Constant(value='outer')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_dependencies.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['a', 'b', 'c', 'd', 'e', 'f', 'g']': Unsupported AST node: List(elts=[Constant(value='a'), Constant(value='b'), Constant(value='c'), Constant(value='d'), Constant(value='e'), Constant(value='f'), Constant(value='g')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_multiple_scopes.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['c1', 'c3']': Unsupported AST node: List(elts=[Constant(value='c1'), Constant(value='c3')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_multiple_scopes.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['c1', 'c2']': Unsupported AST node: List(elts=[Constant(value='c1'), Constant(value='c2')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_temp_effects.py
FUNCTION: test_req
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['c2', 'c3', 'c1']': Unsupported AST node: List(elts=[Constant(value='c2'), Constant(value='c3'), Constant(value='c1')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_temp_effects.py
FUNCTION: test_no_req
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['c2', 'c3']': Unsupported AST node: List(elts=[Constant(value='c2'), Constant(value='c3')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_temp_effects.py
FUNCTION: test_req
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['c1']': Unsupported AST node: List(elts=[Constant(value='c1')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse_temp_effects.py
FUNCTION: test_no_req
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == []': Unsupported AST node: List(elts=[], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_autouse.py
FUNCTION: test_order_and_g
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['a', 'b', 'c', 'd', 'e', 'f', 'g']': Unsupported AST node: List(elts=[Constant(value='a'), Constant(value='b'), Constant(value='c'), Constant(value='d'), Constant(value='e'), Constant(value='f'), Constant(value='g')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/fixtures/test_fixtures_order_scope.py
FUNCTION: test_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == ['session', 'package', 'module', 'class', 'function']': Unsupported AST node: List(elts=[Constant(value='session'), Constant(value='package'), Constant(value='module'), Constant(value='class'), Constant(value='function')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/test_setup_flow_example.py
FUNCTION: teardown_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module.TestStateFullThing.classcount == 0': Unsupported AST node: Attribute(value=Attribute(value=Name(id='module', ctx=Load()), attr='TestStateFullThing', ctx=Load()), attr='classcount', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/test_setup_flow_example.py
FUNCTION: test_42
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.classcount == 1': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='classcount', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/test_setup_flow_example.py
FUNCTION: test_23
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.classcount == 1': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='classcount', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'i.b == 2': Unsupported AST node: Attribute(value=Name(id='i', ctx=Load()), attr='b', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_attribute_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Foo().b == 2': Unsupported AST node: Attribute(value=Call(func=Name(id='Foo', ctx=Load()), args=[], keywords=[]), attr='b', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_attribute_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'i.b == 2': Unsupported AST node: Attribute(value=Name(id='i', ctx=Load()), attr='b', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_attribute_multiple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Foo().b == Bar().b': Unsupported AST node: Attribute(value=Call(func=Name(id='Foo', ctx=Load()), args=[], keywords=[]), attr='b', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f() == g()': Unsupported AST node: Call(func=Name(id='f', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_not
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not f()': Unsupported AST node: Call(func=Name(id='f', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_text
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_similar_text
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_multiline_text
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_long_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a == b': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_long_text_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a == b': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[0, 1, 2] == [0, 1, 3]': Unsupported AST node: List(elts=[Constant(value=0), Constant(value=1), Constant(value=2)], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_list_long
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a == b': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_dict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{'a': 0, 'b': 1, 'c': 0} == {'a': 0, 'b': 2, 'd': 0}': Unsupported AST node: Dict(keys=[Constant(value='a'), Constant(value='b'), Constant(value='c')], values=[Constant(value=0), Constant(value=1), Constant(value=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_set
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{0, 10, 11, 12} == {0, 20, 21}': Unsupported AST node: Set(elts=[Constant(value=0), Constant(value=10), Constant(value=11), Constant(value=12)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_longer_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[1, 2] == [1, 2, 3]': Unsupported AST node: List(elts=[Constant(value=1), Constant(value=2)], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_in_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '1 in [0, 2, 3, 4, 5]': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_not_in_text_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''foo' not in text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_not_in_text_single
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''foo' not in text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_not_in_text_single_long
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''foo' not in text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_not_in_text_single_long_term
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''f' * 70 not in text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_dataclass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_eq_attrs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: func1
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_startswith
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's.startswith(g)': Unsupported AST node: Call(func=Attribute(value=Name(id='s', ctx=Load()), attr='startswith', ctx=Load()), args=[Name(id='g', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_startswith_nested
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f().startswith(g())': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='f', ctx=Load()), args=[], keywords=[]), attr='startswith', ctx=Load()), args=[Call(func=Name(id='g', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_global_func
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(globf(42), float)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Call(func=Name(id='globf', ctx=Load()), args=[Constant(value=42)], keywords=[]), Name(id='float', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.x != 42': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_compare
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'globf(10) < 5': Unsupported AST node: Call(func=Name(id='globf', ctx=Load()), args=[Constant(value=10)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_single_line
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'A.a == b': Unsupported AST node: Attribute(value=Name(id='A', ctx=Load()), attr='a', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'A.a == b': Unsupported AST node: Attribute(value=Name(id='A', ctx=Load()), attr='a', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/failure_demo.py
FUNCTION: test_custom_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a.a == b': Unsupported AST node: Attribute(value=Name(id='a', ctx=Load()), attr='a', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/doc/en/example/assertion/test_failures.py
FUNCTION: test_failure_demo_fails_properly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_simple_unittest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprec.matchreport('testpassing').passed': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='matchreport', ctx=Load()), args=[Constant(value='testpassing')], keywords=[]), attr='passed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_isclasscheck_issue53
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprec.matchreport('test_both', when='call').passed': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='matchreport', ctx=Load()), args=[Constant(value='test_both')], keywords=[keyword(arg='when', value=Constant(value='call'))]), attr='passed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_setUpModule_failing_no_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not call.item.module.values': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Name(id='call', ctx=Load()), attr='item', ctx=Load()), attr='module', ctx=Load()), attr='values', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 0': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_teardown_issue1649
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_method_and_teardown_failing_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_setup_failure_is_shown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_fixtures_setup_setUpClass_issue8394
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_testcase_totally_incompatible_exception_info
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, _pytest.unittest.TestCaseFunction)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Attribute(value=Attribute(value=Name(id='_pytest', ctx=Load()), attr='unittest', ctx=Load()), attr='TestCaseFunction', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_djangolike_testcase
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_unorderable_types
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_unittest_typerror_traceback
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''TypeError' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_unittest_expected_failure_for_failing_test_is_xfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_unittest_expected_failure_for_passing_test_is_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_testcase_handles_init_exceptions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''should raise this exception' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_trace
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(calls) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_pdb_teardown_called
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'teardowns == ['test_pdb_teardown_called.MyTestCase.test_1', 'test_pdb_teardown_called.MyTestCase.test_2']': Unknown symbol: teardowns
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_pdb_teardown_skipped_for_functions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tracked == []': Unknown symbol: tracked
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_pdb_teardown_skipped_for_classes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tracked == []': Unknown symbol: tracked
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_class_cleanups_on_success
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 0': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_class_cleanups_on_setupclass_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 1': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_class_cleanups_on_teardownclass_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed == 3': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_cleanups_on_success
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 0': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_cleanups_on_setup_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 2': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_do_cleanups_on_teardown_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 2': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_traceback_pruning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed == 1': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_raising_unittest_skiptest_during_collection
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed == 0': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_abstract_testcase_is_not_collected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: test_trial_exceptions_with_skips
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unittest.py
FUNCTION: check_call
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args == ('runcall',)': Unknown symbol: args
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_pass_output_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_pass_has_output' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_color_no
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test session starts' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_color_yes_collection_on_non_atty
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test session starts' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_getreportopt
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_REPORTCHARS_DEFAULT == 'fE'': Unknown symbol: _REPORTCHARS_DEFAULT
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_tbstyle_short
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''arg = 42' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_traceconfig
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_terminal_summary_warnings_are_displayed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stdout.count('warning_from_test') == 1': Unsupported AST node: Call(func=Attribute(value=Name(id='stdout', ctx=Load()), attr='count', ctx=Load()), args=[Constant(value='warning_from_test')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_terminal_summary_warnings_header_once
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stdout.count('warning_from_test') == 1': Unsupported AST node: Call(func=Attribute(value=Name(id='stdout', ctx=Load()), attr='count', ctx=Load()), args=[Constant(value='warning_from_test')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_stats
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tr._is_last_item': Unsupported AST node: Attribute(value=Name(id='tr', ctx=Load()), attr='_is_last_item', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_skip_counting_towards_summary
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res == ([('2 failed', {'bold': True, 'red': True})], 'red')': Unknown symbol: res
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_skip_reasons_folding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_full_sequence_print_with_vv
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_force_short_summary
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_format_session_duration
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'format_session_duration(seconds) == expected': Unsupported AST node: Call(func=Name(id='format_session_duration', ctx=Load()), args=[Name(id='seconds', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_format_node_duration
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'format_node_duration(seconds) == expected': Unsupported AST node: Call(func=Name(id='format_node_duration', ctx=Load()), args=[Name(id='seconds', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_raw_skip_reason_skipped
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reason == 'Just so'': Unknown symbol: reason
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_raw_skip_reason_xfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reason == 'To everything there is a season'': Unknown symbol: reason
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_format_trimmed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_format_trimmed(' ({}) ', msg, len(msg) + 4) == ' (unconditional skip) '': Unsupported AST node: Call(func=Name(id='_format_trimmed', ctx=Load()), args=[Constant(value=' ({}) '), Name(id='msg', ctx=Load()), BinOp(left=Call(func=Name(id='len', ctx=Load()), args=[Name(id='msg', ctx=Load())], keywords=[]), op=Add(), right=Constant(value=4))], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_xfail_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expect1) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Name(id='expect1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_xpass_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expect1) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Name(id='expect1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_console_output_style_times_with_skipped_and_passed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''INTERNALERROR' not in combined': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_writeline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not lines[0]': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_report_collect_after_half_a_second
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''= \x1b[32m\x1b[1m2 passed\x1b[0m\x1b[32m in' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_itemreport_directclasses_not_shown_as_subclasses
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_keyboard_in_sessionstart
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f.getvalue() == 'hello' + '\r' + 'hey' + 6 * ' '': Unsupported AST node: Call(func=Attribute(value=Name(id='f', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_report_teststatus_explicit_markup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.stderr.lines': Unsupported AST node: Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_isatty
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tr.isatty() == isatty': Unsupported AST node: Call(func=Attribute(value=Name(id='tr', ctx=Load()), attr='isatty', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_collectonly_fatal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 3': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_collectonly_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_collectonly_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_collectonly_missing_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 4': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_setup_fixture_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_deselected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_deselected_with_hook_wrapper
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_show_deselected_items_using_markexpr_before_test_execution
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_selected_count_with_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_no_skip_summary_if_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.str().find('skip test summary') == -1': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='str', ctx=Load()), args=[], keywords=[]), attr='find', ctx=Load()), args=[Constant(value='skip test summary')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_passes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_verbose_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_verbose_reporting_xdist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_quiet_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test session starts' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_more_quiet_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test session starts' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_f_alias
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expected) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Name(id='expected', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_s_alias
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expected) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Name(id='expected', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_s_folded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expected) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Name(id='expected', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_summary_s_unfolded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines.count(expected[0]) == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), attr='count', ctx=Load()), args=[Subscript(value=Name(id='expected', ctx=Load()), slice=Constant(value=0), ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_tb_crashline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''def test_func2' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_show_capture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''!This is stderr!' not in stdout': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_show_capture_with_teardown_logs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''!stdout!' in result': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: test_times_none_collected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='output', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_terminal.py
FUNCTION: check
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == expected': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_enabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_crash_during_shutdown_captured
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_crash_during_shutdown_not_captured
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_disabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_timeout
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_cancel_timeout_on_hook
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'called == [1]': Unknown symbol: called
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_faulthandler.py
FUNCTION: test_already_initialized_crash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stash.py
FUNCTION: test_stash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(stash) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='stash', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_plugin_already_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.option.plugins == ['terminal']': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='option', ctx=Load()), attr='plugins', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_exclude
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_exclude_glob
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_deselect
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_sessionfinish_with_start
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_basic_testitem_events
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(skipped) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='skipped', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_nested_import_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_raises_output
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(failed) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='failed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_syntax_error_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_exit_first_problem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 1': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_maxfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 2': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_broken_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(len(passed), len(skipped), len(failed)) == (1, 0, 1)': Unsupported AST node: Tuple(elts=[Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[]), Call(func=Name(id='len', ctx=Load()), args=[Name(id='skipped', ctx=Load())], keywords=[]), Call(func=Name(id='len', ctx=Load()), args=[Name(id='failed', ctx=Load())], keywords=[])], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_broken_repr_with_showlocals_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(len(passed), len(skipped), len(failed)) == (0, 0, 1)': Unsupported AST node: Tuple(elts=[Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[]), Call(func=Name(id='len', ctx=Load()), args=[Name(id='skipped', ctx=Load())], keywords=[]), Call(func=Name(id='len', ctx=Load()), args=[Name(id='failed', ctx=Load())], keywords=[])], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_skip_file_by_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_order_of_execution
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == skipped == 0': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_collect_only_with_various_situations
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(itemstarted) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='itemstarted', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_minus_x_import_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(colfail) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='colfail', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_session.py
FUNCTION: test_minus_x_overridden_by_maxfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(colfail) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='colfail', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_nodes.py
FUNCTION: test_subclassing_both_item_and_collector_deprecated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'any((re.search('.*SoWrong.* not using a cooperative constructor.*', x) for x in messages))': Unsupported AST node: Call(func=Name(id='any', ctx=Load()), args=[GeneratorExp(elt=Call(func=Attribute(value=Name(id='re', ctx=Load()), attr='search', ctx=Load()), args=[Constant(value='.*SoWrong.* not using a cooperative constructor.*'), Name(id='x', ctx=Load())], keywords=[]), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Name(id='messages', ctx=Load()), ifs=[], is_async=0)])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_nodes.py
FUNCTION: test__check_initialpaths_for_relpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'nodes._check_initialpaths_for_relpath(initial_paths, cwd) == ''': Unsupported AST node: Call(func=Attribute(value=Name(id='nodes', ctx=Load()), attr='_check_initialpaths_for_relpath', ctx=Load()), args=[Name(id='initial_paths', ctx=Load()), Name(id='cwd', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setupplan.py
FUNCTION: test_show_fixtures_and_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setupplan.py
FUNCTION: test_show_multi_test_fixture_setup_and_teardown_correctly_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setupplan.py
FUNCTION: test_show_multi_test_fixture_setup_and_teardown_same_as_setup_show
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'plan_lines == show_lines': Unknown symbol: plan_lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_hookspec_via_function_attributes_are_deprecated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'record.lineno == DeprecatedHookMarkerSpec.pytest_bad_hook.__code__.co_firstlineno': Unsupported AST node: Attribute(value=Name(id='record', ctx=Load()), attr='lineno', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_hookimpl_via_function_attributes_are_deprecated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'record.lineno == DeprecatedMarkImplPlugin.pytest_runtest_call.__code__.co_firstlineno': Unsupported AST node: Attribute(value=Name(id='record', ctx=Load()), attr='lineno', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_hookproxy_warnings_for_pathlib
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'record.filename == __file__': Unsupported AST node: Attribute(value=Name(id='record', ctx=Load()), attr='filename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_hookimpl_warnings_for_pathlib
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(wc.list) == 5': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='wc', ctx=Load()), attr='list', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_fixture_disallow_on_marked_functions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_fixture_disallow_marks_on_fixtures
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: test_fixture_disallowed_between_marks
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/deprecated_test.py
FUNCTION: fix
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_only_active_fixtures
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_different_scopes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_nested_fixtures
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixtures_with_autouse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixtures_with_parameters
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixtures_with_parameter_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixtures_with_parameter_ids_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_dynamic_fixture_request
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixtures_and_execute_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_setup_show_with_KeyboardInterrupt_in_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_setuponly.py
FUNCTION: test_show_fixture_action_with_bytes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_show
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_gitignore
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'gitignore_path.read_text(encoding='UTF-8') == msg': Unsupported AST node: Call(func=Attribute(value=Name(id='gitignore_path', ctx=Load()), attr='read_text', ctx=Load()), args=[], keywords=[keyword(arg='encoding', value=Constant(value='UTF-8'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_preserve_keys_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'list(read_back.items()) == [('z', 1), ('b', 2), ('a', 3), ('d', 10)]': Unsupported AST node: Call(func=Name(id='list', ctx=Load()), args=[Call(func=Attribute(value=Name(id='read_back', ctx=Load()), attr='items', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_does_not_create_boilerplate_in_existing_dirs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.path.isdir('v')': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='path', ctx=Load()), attr='isdir', ctx=Load()), args=[Constant(value='v')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cachedir_tag
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cachedir_tag_path.read_bytes() == CACHEDIR_TAG_CONTENT': Unsupported AST node: Call(func=Attribute(value=Name(id='cachedir_tag_path', ctx=Load()), attr='read_bytes', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_clioption_with_cacheshow_and_help
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_config_cache_mkdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_dir_permissions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_config_cache_dataerror
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_writefail_cachefile_silent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cache is not None': Unknown symbol: cache
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_writefail_permissions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cache is not None': Unknown symbol: cache
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_failure_warns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_config_cache
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cachefuncarg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_custom_rel_cache_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.path.joinpath(rel_cache_dir).is_dir()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='pytester', ctx=Load()), attr='path', ctx=Load()), attr='joinpath', ctx=Load()), args=[Name(id='rel_cache_dir', ctx=Load())], keywords=[]), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_custom_abs_cache_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'abs_cache_dir.is_dir()': Unsupported AST node: Call(func=Attribute(value=Name(id='abs_cache_dir', ctx=Load()), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_custom_cache_dir_with_env_var
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.path.joinpath('custom_cache_dir').is_dir()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='pytester', ctx=Load()), attr='path', ctx=Load()), attr='joinpath', ctx=Load()), args=[Constant(value='custom_cache_dir')], keywords=[]), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_usecase
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.path.joinpath('.pytest_cache', 'README.md').is_file()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='pytester', ctx=Load()), attr='path', ctx=Load()), attr='joinpath', ctx=Load()), args=[Constant(value='.pytest_cache'), Constant(value='README.md')], keywords=[]), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_xpass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_collectfailure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lastfailed == -1': Unknown symbol: lastfailed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_failure_subset
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lastfailed == -1': Unknown symbol: lastfailed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_creates_cache_when_needed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not os.path.exists('.pytest_cache/v/cache/lastfailed')': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='path', ctx=Load()), attr='exists', ctx=Load()), args=[Constant(value='.pytest_cache/v/cache/lastfailed')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_xfail_not_considered_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.get_cached_last_failed(pytester) == []': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='get_cached_last_failed', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_xfail_strict_considered_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.get_cached_last_failed(pytester) == ['test_xfail_strict_considered_failure.py::test']': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='get_cached_last_failed', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_failed_changed_to_xfail_or_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.get_cached_last_failed(pytester) == ['test_failed_changed_to_xfail_or_skip.py::test']': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='get_cached_last_failed', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: get_cached_last_failed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_cache_cumulative
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.get_cached_last_failed(pytester) == ['test_bar.py::test_bar_2', 'test_foo.py::test_foo_4']': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='get_cached_last_failed', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_no_failures_behavior_all_passed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_args_with_deselected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_with_class_items
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_lastfailed_with_all_filtered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: check_readme
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_readme_passed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.check_readme(pytester) is True': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='check_readme', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: test_readme_failed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.check_readme(pytester) is True': Unsupported AST node: Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='check_readme', ctx=Load()), args=[Name(id='pytester', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: rlf
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_cacheprovider.py
FUNCTION: rlf
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.cache is not None': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='cache', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_matchnodes_two_collections_same_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_exit_on_collection_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 2': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_exit_on_collection_with_maxfail_smaller_than_n_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_exit_on_collection_with_maxfail_bigger_than_n_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 2': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_continue_on_collection_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_continue_on_collection_errors_maxfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_fixture_scope_sibling_conftests
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_handles_raising_on_dunder_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_with_chdir_during_import
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_initial_conftests_with_testpaths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERNAL_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_large_option_breaks_initial_conftests
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_symlink_file_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_symlink_out_of_tree
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collectignore_via_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collector_respects_tbstyle
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_does_not_eagerly_collect_packages
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_does_not_put_src_on_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_fscollector_from_parent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'collector.x == 10': Unsupported AST node: Attribute(value=Name(id='collector', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_class_from_parent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'collector.x == 10': Unsupported AST node: Attribute(value=Name(id='collector', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_does_not_crash_on_error_from_decorated_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_does_not_crash_on_recursive_symlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_short_file_windows
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.parseoutcomes() == {'passed': 1}': Unsupported AST node: Call(func=Attribute(value=Name(id='result', ctx=Load()), attr='parseoutcomes', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_pyargs_collection_tree
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_do_not_collect_symlink_siblings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'symlink_path.is_symlink() is True': Unsupported AST node: Call(func=Attribute(value=Name(id='symlink_path', ctx=Load()), attr='is_symlink', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_yield_disallowed_in_tests
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_annotations_deferred_future
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_annotations_deferred_314
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_versus_item
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not issubclass(Collector, Item)': Unsupported AST node: Call(func=Name(id='issubclass', ctx=Load()), args=[Name(id='Collector', ctx=Load()), Name(id='Item', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_check_equality
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(fn1, pytest.Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='fn1', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_getparent_and_accessors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(cls, pytest.Class)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='cls', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Class', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_getcustomfile_roundtrip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(node, pytest.File)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='node', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='File', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_ignored_certain_directories
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_notfound' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_ignored_virtualenvs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_invenv' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_ignored_virtualenvs_norecursedirs_precedence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_invenv' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test__in_venv
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_in_venv(base_path) is False': Unsupported AST node: Call(func=Name(id='_in_venv', ctx=Load()), args=[Name(id='base_path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_testpaths_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[x.name for x in items] == ['test_b', 'test_c']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='name', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Name(id='items', ctx=Load()), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_missing_permissions_on_unselected_directory_doesnt_crash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_pytest_collect_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(wascalled) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='wascalled', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_ignore_collect_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_ignore_collect_not_called_on_argument
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collectignore_exclude_on_option
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collectignoreglob_exclude_on_option
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_topdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'topdir == rcol.path': Unknown symbol: topdir
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_protocol_single_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'item.name == 'test_func'': Unsupported AST node: Attribute(value=Name(id='item', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_custom_nodes_multi_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_subdir_event_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_two_commandline_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_serialization_byid
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_find_byid_without_instance_parents
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_collect_parametrized_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_global_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(col, pytest.Module)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='col', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Module', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_pkgfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'col is not None': Unknown symbol: col
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_check_collect_hashes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_example_items1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_classmethod_is_discovered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ids == ['TestCase.test_classmethod']': Unknown symbol: ids
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_class_and_functions_discovery_using_glob
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ids == ['MyTestSuite.x_test', 'TestCase.test_y']': Unknown symbol: ids
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_no_under
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'modcol.name in values': Unsupported AST node: Attribute(value=Name(id='modcol', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_duplicates_handled_correctly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'item.parent is not None and item.parent.parent is not None': Unsupported AST node: Attribute(value=Name(id='item', ctx=Load()), attr='parent', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_unpacked_marks_added_to_keywords
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, pytest.Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collection.py
FUNCTION: test_custom_directory_example
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(calls) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/typing_raises_group.py
FUNCTION: check_raisesexc_typevar_default
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'e.expected_exceptions is not None': Unsupported AST node: Attribute(value=Name(id='e', ctx=Load()), attr='expected_exceptions', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/typing_raises_group.py
FUNCTION: check_multiple_exceptions_1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'd': Unknown symbol: d
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/typing_raises_group.py
FUNCTION: check_multiple_exceptions_2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'd': Unknown symbol: d
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: test_get_real_func
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_real_func(wrapped_func) is func': Unsupported AST node: Call(func=Name(id='get_real_func', ctx=Load()), args=[Name(id='wrapped_func', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: test_get_real_func_partial
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_real_func(foo) is foo': Unsupported AST node: Call(func=Name(id='get_real_func', ctx=Load()), args=[Name(id='foo', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: test_safe_getattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'safe_getattr(helper, 'raise_exception', 'default') == 'default'': Unsupported AST node: Call(func=Name(id='safe_getattr', ctx=Load()), args=[Name(id='helper', ctx=Load()), Constant(value='raise_exception'), Constant(value='default')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: test_safe_isclass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'safe_isclass(type) is True': Unsupported AST node: Call(func=Name(id='safe_isclass', ctx=Load()), args=[Name(id='type', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: test_cached_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ncalls == 0': Unknown symbol: ncalls
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_compat.py
FUNCTION: __class__
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capture_conftest_runtest_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capture_early_option_parsing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_dontreadfrominput
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f.buffer is f': Unsupported AST node: Attribute(value=Name(id='f', ctx=Load()), attr='buffer', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_captureresult
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(cr) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='cr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: lsof_check
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len2 < len1 + 3': Unknown symbol: len2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_using_capsys_fixture_works_with_sys_stdout_encoding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capsys_results_accessible_by_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'capture_result.out == 'spam'': Unsupported AST node: Attribute(value=Name(id='capture_result', ctx=Load()), attr='out', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_fdcapture_tmpfile_remains_the_same
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(cap.err, capture.FDCapture)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='cap', ctx=Load()), attr='err', ctx=Load()), Attribute(value=Name(id='capture', ctx=Load()), attr='FDCapture', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_and_logging_fundamentals
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''atexit' not in result.stderr.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_crash_on_closing_tmpfile_py27
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_global_capture_with_live_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capture_with_live_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_typeerror_encodedfile_write
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result_with_capture.ret == result_without_capture.ret': Unsupported AST node: Attribute(value=Name(id='result_with_capture', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_stderr_write_returns_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys.stderr.write('Foo') == 3': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='sys', ctx=Load()), attr='stderr', ctx=Load()), attr='write', ctx=Load()), args=[Constant(value='Foo')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_encodedfile_writelines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ef.writelines(['line3', 'line4']) is None': Unsupported AST node: Call(func=Attribute(value=Name(id='ef', ctx=Load()), attr='writelines', ctx=Load()), args=[List(elts=[Constant(value='line3'), Constant(value='line4')], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test__get_multicapture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(_get_multicapture('no'), MultiCapture)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Call(func=Name(id='_get_multicapture', ctx=Load()), args=[Constant(value='no')], keywords=[]), Name(id='MultiCapture', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_logging_while_collecting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_libedit_workaround
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'match is not None': Unknown symbol: match
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_no_carry_over
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''in func1' not in s': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_logging_stream_ownership
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stderr.str().find('atexit') == -1': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='str', ctx=Load()), args=[], keywords=[]), attr='find', ctx=Load()), args=[Constant(value='atexit')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_conftestlogging_is_shown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_conftestlogging_and_test_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_logging_after_cap_stopped
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capteesys
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_cafd_preserves_newlines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out.endswith(nl)': Unsupported AST node: Call(func=Attribute(value=Name(id='out', ctx=Load()), attr='endswith', ctx=Load()), args=[Name(id='nl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_keyboardinterrupt_disables_capturing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capture_and_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''closed' not in result.stderr.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == 'hello'': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_write_bytes_to_buffer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f.getvalue() == 'foo\r\n'': Unsupported AST node: Call(func=Attribute(value=Name(id='f', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's1 == 'hello'': Unknown symbol: s1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == 'hello'': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_stderr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == 'hello\n'': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_stdin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == b''': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_writeorg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'scap == data1.decode('ascii')': Unknown symbol: scap
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capfd_sys_stdout_mode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''b' not in sys.stdout.mode': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_done_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hello'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_reset_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hello world\n'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_readouterr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'err == 'error2'': Unknown symbol: err
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capture_results_accessible_by_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'capture_result.out == 'hello'': Unsupported AST node: Attribute(value=Name(id='capture_result', ctx=Load()), attr='out', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_readouterr_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hxąć\n'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_reset_twice_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hello\n'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_modify_sysouterr_in_between
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hello'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_error_recursive
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out1 == 'cap1\n'': Unknown symbol: out1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_just_out_capture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == 'hello'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_just_err_capture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'err == 'world'': Unknown symbol: err
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_stdin_restored
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newstdin != sys.stdin': Unknown symbol: newstdin
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_capturing_error_recursive
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out1 == 'cap1\ncap2\n'': Unknown symbol: out1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_intermingling
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == '123'': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_capture.py
FUNCTION: test_stdcapture_fd_invalid_fd
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_wrap_session_notify_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines[0] == 'INTERNALERROR> Traceback (most recent call last):'': Unsupported AST node: Subscript(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_wrap_session_exit_sessionfinish
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines[-1] == 'collected 0 items'': Unsupported AST node: Subscript(value=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load()), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_module_full_path_without_drive
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fn.is_file()': Unsupported AST node: Call(func=Attribute(value=Name(id='fn', ctx=Load()), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_collection_argument(invocation_path, 'src/pkg/test.py') == CollectionArgument(path=invocation_path / 'src/pkg/test.py', parts=[], module_name=None)': Unsupported AST node: Call(func=Name(id='resolve_collection_argument', ctx=Load()), args=[Name(id='invocation_path', ctx=Load()), Constant(value='src/pkg/test.py')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_collection_argument(invocation_path, 'src/pkg') == CollectionArgument(path=invocation_path / 'src/pkg', parts=[], module_name=None)': Unsupported AST node: Call(func=Name(id='resolve_collection_argument', ctx=Load()), args=[Name(id='invocation_path', ctx=Load()), Constant(value='src/pkg')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_pypath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_collection_argument(invocation_path, 'pkg.test', as_pypath=True) == CollectionArgument(path=invocation_path / 'src/pkg/test.py', parts=[], module_name='pkg.test')': Unsupported AST node: Call(func=Name(id='resolve_collection_argument', ctx=Load()), args=[Name(id='invocation_path', ctx=Load()), Constant(value='pkg.test')], keywords=[keyword(arg='as_pypath', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_parametrized_name_with_colons
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_collection_argument(invocation_path, 'src/pkg/test.py::test[a::b]') == CollectionArgument(path=invocation_path / 'src/pkg/test.py', parts=['test[a::b]'], module_name=None)': Unsupported AST node: Call(func=Name(id='resolve_collection_argument', ctx=Load()), args=[Name(id='invocation_path', ctx=Load()), Constant(value='src/pkg/test.py::test[a::b]')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_main.py
FUNCTION: test_absolute_paths_are_resolved_correctly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_collection_argument(invocation_path, full_path) == CollectionArgument(path=Path(os.path.abspath('src')), parts=[], module_name=None)': Unsupported AST node: Call(func=Name(id='resolve_collection_argument', ctx=Load()), args=[Name(id='invocation_path', ctx=Load()), Name(id='full_path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_item_fspath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_testdir_testtmproot
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'testdir.test_tmproot.check(dir=1)': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='testdir', ctx=Load()), attr='test_tmproot', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_testdir_makefile_dot_prefixes_extension_silently
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''.foo.bar' in str(p1)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_testdir_makefile_ext_empty_string_makes_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_testdir_makefile' in str(p1)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_tmpdir_factory
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(tmpdir_factory.getbasetemp()) == str(tmp_path_factory.getbasetemp())': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Attribute(value=Name(id='tmpdir_factory', ctx=Load()), attr='getbasetemp', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_tmpdir_equals_tmp_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Path(tmpdir) == tmp_path': Unsupported AST node: Call(func=Name(id='Path', ctx=Load()), args=[Name(id='tmpdir', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_tmpdir_always_is_realpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_cache_makedir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'dir.exists()': Unsupported AST node: Call(func=Attribute(value=Name(id='dir', ctx=Load()), attr='exists', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_fixturerequest_getmodulepath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, pytest.Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_legacypath.py
FUNCTION: test_addini_paths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unhandled_thread_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unhandled_thread_exception_in_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unhandled_thread_exception_in_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unhandled_thread_exception_warning_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_threadexception_warning_multiple_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unraisable_collection_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_unhandled_thread_exception_after_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.INTERNAL_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_threadexception.py
FUNCTION: test_possibly_none_excinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warning_types.py
FUNCTION: test_warning_types
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'warning_class.__module__ == 'pytest'': Unsupported AST node: Attribute(value=Name(id='warning_class', ctx=Load()), attr='__module__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_recwarn_stacklevel
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'warn.filename == __file__': Unsupported AST node: Attribute(value=Name(id='warn', ctx=Load()), attr='filename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_recwarn_captures_deprecation_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(recwarn) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='recwarn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_pop_finds_exact_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_pop_finds_best_inexact_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_warn.category is self.ChildWarning': Unsupported AST node: Attribute(value=Name(id='_warn', ctx=Load()), attr='category', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_deprecated_call_ret
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ret == 42': Unknown symbol: ret
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_deprecated_call_preserves
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'onceregistry == warnings.onceregistry': Unknown symbol: onceregistry
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_as_contextmanager
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(excinfo.value) == expected_str': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_record
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_record_only
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_record_by_subclass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(record) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='record', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_can_capture_previously_warned
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f() == 10': Unsupported AST node: Call(func=Name(id='f', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_warns_context_manager_with_kwargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Unexpected keyword arguments' in str(excinfo.value)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_skip_within_warns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_fail_within_warns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_exit_within_warns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_recwarn.py
FUNCTION: test_keyboard_interrupt_within_warns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_custom_prog
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'parser._getparser().prog == argparse.ArgumentParser().prog': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='parser', ctx=Load()), attr='_getparser', ctx=Load()), args=[], keywords=[]), attr='prog', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_argument
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'argument._short_opts == ['-t']': Unsupported AST node: Attribute(value=Name(id='argument', ctx=Load()), attr='_short_opts', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_argument_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'argument.type is int': Unsupported AST node: Attribute(value=Name(id='argument', ctx=Load()), attr='type', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_argument_processopt
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res['default'] == 42': Unsupported AST node: Subscript(value=Name(id='res', ctx=Load()), slice=Constant(value='default'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_group_add_and_get
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'group.name == 'hello'': Unsupported AST node: Attribute(value=Name(id='group', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_getgroup_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'group.name == 'hello'': Unsupported AST node: Attribute(value=Name(id='group', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_group_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'groups_names == list('132')': Unknown symbol: groups_names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_group_addoption
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(group.options) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='group', ctx=Load()), attr='options', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_group_addoption_conflict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str({'--option1'}) in str(err.value)': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Set(elts=[Constant(value='--option1')])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_group_shortopt_lowercase
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(group.options) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='group', ctx=Load()), attr='options', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parser_addoption
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(group.options) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='group', ctx=Load()), attr='options', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args.hello == 'world'': Unsupported AST node: Attribute(value=Name(id='args', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(args, parseopt.FILE_OR_DIR)[0] == '.'': Unsupported AST node: Subscript(value=Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='args', ctx=Load()), Attribute(value=Name(id='parseopt', ctx=Load()), attr='FILE_OR_DIR', ctx=Load())], keywords=[]), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_from_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(args, parseopt.FILE_OR_DIR) == tests': Unsupported AST node: Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='args', ctx=Load()), Attribute(value=Name(id='parseopt', ctx=Load()), attr='FILE_OR_DIR', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_known_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ns.hello': Unsupported AST node: Attribute(value=Name(id='ns', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_known_and_unknown_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ns.hello': Unsupported AST node: Attribute(value=Name(id='ns', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_will_set_default
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'option.hello == 'x'': Unsupported AST node: Attribute(value=Name(id='option', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_setoption
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'option.hello == 'world'': Unsupported AST node: Attribute(value=Name(id='option', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_special_destination
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args.ultimate_answer == 42': Unsupported AST node: Attribute(value=Name(id='args', ctx=Load()), attr='ultimate_answer', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_split_positional_arguments
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(args, parseopt.FILE_OR_DIR) == ['4', '2']': Unsupported AST node: Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='args', ctx=Load()), Attribute(value=Name(id='parseopt', ctx=Load()), attr='FILE_OR_DIR', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_parse_defaultgetter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'option.hello == 'world'': Unsupported AST node: Attribute(value=Name(id='option', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_drop_short_helper
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args.twoword == 'hallo'': Unsupported AST node: Attribute(value=Name(id='args', ctx=Load()), attr='twoword', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_drop_short_2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args.func_arg is True': Unsupported AST node: Attribute(value=Name(id='args', ctx=Load()), attr='func_arg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_drop_short_3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'args.func_arg is False': Unsupported AST node: Attribute(value=Name(id='args', ctx=Load()), attr='func_arg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_drop_short_help0
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''--func-args, --doit  foo' in help': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_drop_short_help1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''-doit, --func-args  foo' in help': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_parseopt.py
FUNCTION: test_multiple_metavar_help
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''--preferences=value1 value2 value3' in help': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_doubledash_considered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_issue151_load_all_conftests
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(set(pm.get_plugins()) - {pm}) == len(names)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[BinOp(left=Call(func=Name(id='set', ctx=Load()), args=[Call(func=Attribute(value=Name(id='pm', ctx=Load()), attr='get_plugins', ctx=Load()), args=[], keywords=[])], keywords=[]), op=Sub(), right=Set(elts=[Name(id='pm', ctx=Load())]))], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_global_import
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftestcutdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftestcutdir_inplace_considered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_installed_conftest_is_picked_up
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_symlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_symlink_files
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_badcase
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_uppercase
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_no_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_import_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mods == expected': Unknown symbol: mods
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_issue1073_conftest_special_objects
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_conftest_exception_handling
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 4': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_required_option_help
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''general:' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_basic_init
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'conftest._rget_with_confmod('a', p)[1] == 1': Unsupported AST node: Subscript(value=Call(func=Attribute(value=Name(id='conftest', ctx=Load()), attr='_rget_with_confmod', ctx=Load()), args=[Constant(value='a'), Name(id='p', ctx=Load())], keywords=[]), slice=Constant(value=1), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_immediate_initialization_and_incremental_are_the_same
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not len(conftest._dirpath2confmods)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='conftest', ctx=Load()), attr='_dirpath2confmods', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_value_access_by_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'conftest._rget_with_confmod('a', adir)[1] == 1': Unsupported AST node: Subscript(value=Call(func=Attribute(value=Name(id='conftest', ctx=Load()), attr='_rget_with_confmod', ctx=Load()), args=[Constant(value='a'), Name(id='adir', ctx=Load())], keywords=[]), slice=Constant(value=1), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_conftest.py
FUNCTION: test_value_access_with_confmod
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'value == 1.5': Unknown symbol: value
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: runpdb_and_get_report
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_trace_after_runpytest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_quit_with_swallowed_SystemExit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''no tests ran' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_suspends_fixture_capturing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f'> PDB set_trace (IO-capturing turned off for fixture {fixture}) >' in before': Unsupported AST node: JoinedStr(values=[Constant(value='> PDB set_trace (IO-capturing turned off for fixture '), FormattedValue(value=Name(id='fixture', ctx=Load()), conversion=-1), Constant(value=') >')])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdbcls_via_local_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_raises_bdbquit_with_eoferror
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_wrapper_class_is_reused
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_xfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''xfail' in rep.keywords': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.skipped': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='skipped', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_top_level_raise_skiptest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''entering PDB' not in stdout': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_BdbQuit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_on_KeyboardInterrupt
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: flush
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not child.isalive()': Unsupported AST node: Call(func=Attribute(value=Name(id='child', ctx=Load()), attr='isalive', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_unittest_postmortem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''debug.me' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_print_captured_stdout_and_stderr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Exit: Quitting debugger' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_dont_print_empty_captured_stdout_and_stderr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''captured stdout' not in output': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_print_captured_logs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''1 failed' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_print_captured_logs_nologging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''captured log' not in output': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_interaction_on_internal_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len([x for x in child.before.decode().splitlines() if x.startswith('INTERNALERROR> Traceback')]) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[ListComp(elt=Name(id='x', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='child', ctx=Load()), attr='before', ctx=Load()), attr='decode', ctx=Load()), args=[], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[]), ifs=[Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='startswith', ctx=Load()), args=[Constant(value='INTERNALERROR> Traceback')], keywords=[])], is_async=0)])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_interaction_capturing_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''AssertionError' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_set_trace_kwargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''PDB set_trace' not in child.before.decode()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_set_trace_interception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''no tests ran' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_interaction_doctest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''UNEXPECTED EXCEPTION: AssertionError()' in child.before.decode('utf8')': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_doctest_set_trace_quit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''! _pytest.outcomes.Exit: Quitting debugger !' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_interaction_capturing_twice
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Captured stdout call' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_with_injected_do_debug
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b'PDB continue' not in child.before': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_continue_with_recursive_debug
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''\r\nENTERING RECURSIVE DEBUGGER\r\n' in before': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_enter_leave_pdb_hooks_are_called
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''leave_pdb_hook' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_custom_cls
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'custom_pdb_calls == ['init', 'reset', 'interaction']': Unsupported AST node: List(elts=[Constant(value='init'), Constant(value='reset'), Constant(value='interaction')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_validate_usepdb_cls
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_validate_usepdb_cls('os.path:dirname.__name__') == ('os.path', 'dirname.__name__')': Unsupported AST node: Call(func=Name(id='_validate_usepdb_cls', ctx=Load()), args=[Constant(value='os.path:dirname.__name__')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_custom_cls_without_pdb
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'custom_pdb_calls == []': Unsupported AST node: List(elts=[], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_wrapped_commands_docstrings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Undocumented commands' not in child.before.decode()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_custom_cls
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'custom_debugger_hook == ['init', 'set_trace']': Unsupported AST node: List(elts=[Constant(value='init'), Constant(value='set_trace')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_sys_breakpoint_interception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Quitting debugger' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_pdb_not_altered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''1 failed' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_trace_sets_breakpoint
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''= 2 passed in' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_debugging.py
FUNCTION: test_trace_with_parametrize_handles_shared_fixtureinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''= 6 passed in' in rest': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_zipimport_hook
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_import_plugin_unicode_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'r.ret == 0': Unsupported AST node: Attribute(value=Name(id='r', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_fixture_order_respects_scope
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_usage_error_code
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_pdb_can_be_rewritten
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_tee_stdio_captures_and_live_prints
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''@this is stdout@\n' in fullXml': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_no_brokenpipeerror_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'popen.stderr.read() == b''': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='popen', ctx=Load()), attr='stderr', ctx=Load()), attr='read', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_no_terminal_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_stop_iteration_from_collect
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_stop_iteration_runtest_protocol
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_config_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_root_conftest_syntax_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_early_hook_error_issue38_1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_early_hook_configure_error_issue38
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_file_not_found
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_file_not_found_unconfigure_issue143
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_config_preparse_plugin_option
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_assertion_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_nested_import_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_not_collectable_arguments
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_better_reporting_on_conftest_load_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines == []': Unsupported AST node: Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_early_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_issue93_initialnode_importing_capturing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_conftest_printing_shows_if_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_issue109_sibling_conftests_not_loaded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_directory_skipped
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_multiple_items_per_collector_byid
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_skip_on_generated_funcarg_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_direct_addressing_selects
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_direct_addressing_notfound
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_initialization_error_issue49
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 3': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_report_all_failed_collections_initargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_namespace_import_doesnt_confuse_import_hook
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_plugins_given_as_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''invalid' in str(excinfo.value)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_earlyinit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_pydoc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_import_star_pytest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_python_minus_m_invocation_ok
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_python_minus_m_invocation_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_python_pytest_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_invoke_with_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'retcode == ExitCode.NO_TESTS_COLLECTED': Unknown symbol: retcode
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_invoke_plugin_api
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''--myopt' in out': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_pyargs_importerror
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_pyargs_only_imported_once
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.outlines.count('hello from test_foo') == 1': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='outlines', ctx=Load()), attr='count', ctx=Load()), args=[Constant(value='hello from test_foo')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_pyargs_filename_looks_like_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_cmdline_python_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_cmdline_python_legacy_namespace_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_cmdline_python_package_symlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_cmdline_python_package_not_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_core_backward_compatibility
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'type(_pytest.config.get_plugin_manager()) is _pytest.config.PytestPluginManager': Unsupported AST node: Call(func=Name(id='type', ctx=Load()), args=[Call(func=Attribute(value=Attribute(value=Name(id='_pytest', ctx=Load()), attr='config', ctx=Load()), attr='get_plugin_manager', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_has_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'request.config.pluginmanager.hasplugin('python')': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Attribute(value=Name(id='request', ctx=Load()), attr='config', ctx=Load()), attr='pluginmanager', ctx=Load()), attr='hasplugin', ctx=Load()), args=[Constant(value='python')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls_show_2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls_showall
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls_showall_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls_showall_durationsmin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_calls_showall_durationsmin_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: check_tests_in_output
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'found_test_numbers == set(expected_test_numbers)': Unknown symbol: found_test_numbers
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_with_deselected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_with_failing_collection
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_with_not
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/acceptance_test.py
FUNCTION: test_setup_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_argcomplete.py
FUNCTION: test_compare_with_compgen
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'equal_with_bash('', ffc, fc, out=sys.stdout)': Unsupported AST node: Call(func=Name(id='equal_with_bash', ctx=Load()), args=[Constant(value=''), Name(id='ffc', ctx=Load()), Name(id='fc', ctx=Load())], keywords=[keyword(arg='out', value=Attribute(value=Name(id='sys', ctx=Load()), attr='stdout', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_fail_and_continue_with_stepwise
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strip_resource_warnings(result.stderr.lines) == []': Unsupported AST node: Call(func=Name(id='_strip_resource_warnings', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_run_with_skip_option
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strip_resource_warnings(result.stderr.lines) == []': Unsupported AST node: Call(func=Name(id='_strip_resource_warnings', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_fail_on_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strip_resource_warnings(result.stderr.lines) == []': Unsupported AST node: Call(func=Name(id='_strip_resource_warnings', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_change_testfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strip_resource_warnings(result.stderr.lines) == []': Unsupported AST node: Call(func=Name(id='_strip_resource_warnings', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_stepwise_xdist_dont_store_lastfailed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_disabled_stepwise_xdist_dont_clear_cache
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_stepwise.py
FUNCTION: test_cache_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cache_file.is_file()': Unsupported AST node: Call(func=Attribute(value=Name(id='cache_file', ctx=Load()), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_version_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_version_less_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_versions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(pytest.__version__, str)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='pytest', ctx=Load()), attr='__version__', ctx=Load()), Name(id='str', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_help
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_empty_help_param
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_hookvalidation_unknown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_hookvalidation_optional
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_debug
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_helpconfig.py
FUNCTION: test_PYTEST_DEBUG
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_empty_is_false
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not evaluate('', lambda ident: False)': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Constant(value=''), Lambda(args=arguments(posonlyargs=[], args=[arg(arg='ident')], kwonlyargs=[], kw_defaults=[], defaults=[]), body=Constant(value=False))], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_basic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(expr, matcher) is expected': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='expr', ctx=Load()), Name(id='matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_syntax_oddities
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(expr, matcher) is expected': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='expr', ctx=Load()), Name(id='matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_backslash_not_treated_specially
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate('\\nfoo\\n', matcher)': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Constant(value='\\nfoo\\n'), Name(id='matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_syntax_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.value.column == column': Unsupported AST node: Attribute(value=Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load()), attr='column', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_valid_idents
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(ident, {ident: True}.__getitem__)': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='ident', ctx=Load()), Attribute(value=Dict(keys=[Name(id='ident', ctx=Load())], values=[Constant(value=True)]), attr='__getitem__', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_keyword_expressions_with_numbers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(expr, mark_matcher) is expected': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='expr', ctx=Load()), Name(id='mark_matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_builtin_matchers_keyword_expressions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(expr, mark_matcher) is expected': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='expr', ctx=Load()), Name(id='mark_matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark_expression.py
FUNCTION: test_str_keyword_expressions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'evaluate(expr, mark_matcher) is expected': Unsupported AST node: Call(func=Name(id='evaluate', ctx=Load()), args=[Name(id='expr', ctx=Load()), Name(id='mark_matcher', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_setattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'A.y == 2': Unsupported AST node: Attribute(value=Name(id='A', ctx=Load()), attr='y', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_delattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not hasattr(A, 'x')': Unsupported AST node: Call(func=Name(id='hasattr', ctx=Load()), args=[Name(id='A', ctx=Load()), Constant(value='x')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_setitem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'd['x'] == 2': Unsupported AST node: Subscript(value=Name(id='d', ctx=Load()), slice=Constant(value='x'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_setitem_deleted_meanwhile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not d': Unknown symbol: d
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_delitem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''x' not in d': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_setenv
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.environ['XYZ123'] == '2'': Unsupported AST node: Subscript(value=Attribute(value=Name(id='os', ctx=Load()), attr='environ', ctx=Load()), slice=Constant(value='XYZ123'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_delenv
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'name not in os.environ': Unknown symbol: name
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_setenv_prepend
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.environ['XYZ123'] == '3-2'': Unsupported AST node: Subscript(value=Attribute(value=Name(id='os', ctx=Load()), attr='environ', ctx=Load()), slice=Constant(value='XYZ123'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_monkeypatch_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tuple(res) == (1, 0, 0)': Unsupported AST node: Call(func=Name(id='tuple', ctx=Load()), args=[Name(id='res', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_syspath_prepend
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys.path[0] == 'hello'': Unsupported AST node: Subscript(value=Attribute(value=Name(id='sys', ctx=Load()), attr='path', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_chdir_with_path_local
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.getcwd() == str(tmp_path)': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='getcwd', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_chdir_with_str
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.getcwd() == str(tmp_path)': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='getcwd', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_chdir_undo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.getcwd() == cwd': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='getcwd', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_chdir_double_undo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.getcwd() == str(tmp_path)': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='getcwd', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_issue156_undo_staticmethod
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Sample.hello is None': Unsupported AST node: Attribute(value=Name(id='Sample', ctx=Load()), attr='hello', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_undo_class_descriptors_delattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(SampleParent, 'hello', None) is None': Unsupported AST node: Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='SampleParent', ctx=Load()), Constant(value='hello'), Constant(value=None)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_context
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'inspect.isclass(functools.partial)': Unsupported AST node: Call(func=Attribute(value=Name(id='inspect', ctx=Load()), attr='isclass', ctx=Load()), args=[Attribute(value=Name(id='functools', ctx=Load()), attr='partial', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_context_classmethod
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'A.x == 1': Unsupported AST node: Attribute(value=Name(id='A', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_monkeypatch.py
FUNCTION: test_syspath_prepend_with_namespace_packages
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ns_pkg.hello.check() == 'hello'': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='ns_pkg', ctx=Load()), attr='hello', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_xdist_longrepr_to_str_issue_241
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 6': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_xdist_report_longrepr_reprcrash_130
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_reprentries_serialization_170
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_reprentries_serialization_196
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_itemreport_outcomes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 17': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_collectreport_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reports': Unknown symbol: reports
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_extended_report_deserialization
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reports': Unknown symbol: reports
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_paths_support
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_deserialization_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_chained_exceptions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'report.failed': Unsupported AST node: Attribute(value=Name(id='report', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_chained_exceptions_no_reprcrash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_report_timestamps_match_duration
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_test_report
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 6': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_collect_report
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: test_invalid_report_types
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reports': Unknown symbol: reports
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: check_longrepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(longrepr, ExceptionChainRepr)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='longrepr', ctx=Load()), Name(id='ExceptionChainRepr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_reports.py
FUNCTION: check_longrepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(longrepr, ExceptionChainRepr)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='longrepr', ctx=Load()), Name(id='ExceptionChainRepr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_python25_compile_issue257
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_rewritten
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_reprcompare_notin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callop('not in', 'foo', 'aaafoobbb') == ["'foo' not in 'aaafoobbb'", '', "'foo' is contained here:", '  aaafoobbb', '?    +++']': Unsupported AST node: Call(func=Name(id='callop', ctx=Load()), args=[Constant(value='not in'), Constant(value='foo'), Constant(value='aaafoobbb')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_reprcompare_whitespaces
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callequal('\r\n', '\n') == ["'\\r\\n' == '\\n'", '', 'Strings contain only whitespace, escaping them using repr()', "- '\\n'", "+ '\\r\\n'", '?  ++']': Unsupported AST node: Call(func=Name(id='callequal', ctx=Load()), args=[Constant(value='\r\n'), Constant(value='\n')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_assertion_options
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''3 == 4' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_assert_tuple_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg not in result.stdout.str()': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_assert_indirect_tuple_no_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''WR1' not in output': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_issue_1944
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '"AttributeError: 'Module' object has no attribute '_obj'" not in result.stdout.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_reprcompare_verbose_long
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_verbose_exposes_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity() == TestMockConfig.SOME_VERBOSITY_LEVEL': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_get_assertion_override_not_set_verbose_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity(_Config.VERBOSITY_ASSERTIONS) == TestMockConfig.SOME_VERBOSITY_LEVEL': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[Attribute(value=Name(id='_Config', ctx=Load()), attr='VERBOSITY_ASSERTIONS', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_get_assertion_override_set_custom_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity(_Config.VERBOSITY_ASSERTIONS) == TestMockConfig.SOME_OTHER_VERBOSITY_LEVEL': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[Attribute(value=Name(id='_Config', ctx=Load()), attr='VERBOSITY_ASSERTIONS', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_pytest_plugins_rewrite_module_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_pytest_plugins_rewrite_module_names_correctly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_different_types
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callequal([0, 1], 'foo') is None': Unsupported AST node: Call(func=Name(id='callequal', ctx=Load()), args=[List(elts=[Constant(value=0), Constant(value=1)], ctx=Load()), Constant(value='foo')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_summary
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_text_diff
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callequal('spam', 'eggs') == ["'spam' == 'eggs'", '', '- eggs', '+ spam']': Unsupported AST node: Call(func=Name(id='callequal', ctx=Load()), args=[Constant(value='spam'), Constant(value='eggs')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_text_skipping
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_text_skipping_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_multiline_text_diff
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff is not None': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_bytes_diff_normal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["b'spam' == b'eggs'", '', "At index 0 diff: b's' != b'e'", 'Use -v to get more diff']': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_bytes_diff_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["b'spam' == b'eggs'", '', "At index 0 diff: b's' != b'e'", '', 'Full diff:', "- b'eggs'", "+ b'spam'"]': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_iterable_full_diff
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_iterable_quiet
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl == ['[1, 2] == [10, 2]', '', 'At index 0 diff: 1 != 10', 'Use -v to get more diff']': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_different_lengths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_wrap_for_multiple_lines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["['a', 'b', 'c'] == ['a', 'b', 'c...dddddddddddd']", '', "Right contains one more item: '" + long_d + "'", '', 'Full diff:', '  [', "      'a',", "      'b',", "      'c',", "-     '" + long_d + "',", '  ]']': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_wrap_for_width_rewrap_same_length
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["['aaaaaaaaaaa...cccccccccccc'] == ['bbbbbbbbbbb...aaaaaaaaaaaa']", '', "At index 0 diff: 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' != 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'", '', 'Full diff:', '  [', "+     'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',", "      'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',", "      'cccccccccccccccccccccccccccccc',", "-     'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',", '  ]']': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_dont_wrap_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["['a', 'aaaaaa...aaaaaaa', ...] == ['should not get wrapped']", '', "At index 0 diff: 'a' != 'should not get wrapped'", "Left contains 7 more items, first extra item: 'aaaaaaaaaa'", '', 'Full diff:', '  [', "-     'should not get wrapped',", "+     'a',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", "+     'aaaaaaaaaa',", '  ]']': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict_wrap
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'diff == ["{'common': 1,...1, 'env2': 2}} == {'common': 1,...: {'env1': 1}}", '', 'Omitting 1 identical items, use -vv to show', 'Differing items:', "{'env': {'env1': 1, 'env2': 2}} != {'env': {'env1': 1}}", '', 'Full diff:', '  {', "      'common': 1,", "      'env': {", "          'env1': 1,", "+         'env2': 2,", '      },', '  }']': Unknown symbol: diff
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict_omitting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict_omitting_with_verbosity_1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict_omitting_with_verbosity_2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_dict_different_items
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines == ["{'a': 0} == {'b': 1, 'c': 2}", '', 'Left contains 1 more item:', "{'a': 0}", 'Right contains 2 more items:', "{'b': 1, 'c': 2}", '', 'Full diff:', '  {', "-     'b': 1,", '?      ^   ^', "+     'a': 0,", '?      ^   ^', "-     'c': 2,", '  }']': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_sequence_different_items
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines == ['(1, 2) == (3, 4, 5)', '', 'At index 0 diff: 1 != 3', 'Right contains one more item: 5', '', 'Full diff:', '  (', '-     3,', '?     ^', '+     1,', '?     ^', '-     4,', '?     ^', '+     2,', '?     ^', '-     5,', '  )']': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_set
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_frozenzet
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_Sequence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_tuples
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_list_bad_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_one_repr_empty
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_repr_no_exc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callequal('£€', '£') == ["'£€' == '£'", '', '- £', '+ £€']': Unsupported AST node: Call(func=Name(id='callequal', ctx=Load()), args=[Constant(value='£€'), Constant(value='£')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_nonascii_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl == ["ÿ == '1'", '', '- 1']': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_format_nonascii_explanation
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation('λ')': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Constant(value='λ')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_mojibake
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl is not None': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_nfc_nfd_same_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expl == ["'hyv\\xe4' == 'hyva\\u0308'", '', f'- {right!s}', f'+ {left!s}']': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_recursive
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_recursive_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_with_attribute_comparison_off
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is not None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_comparing_two_different_attrs_classes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_with_auto_detect_and_custom_eq
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_attrs_with_custom_eq
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines is None': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_namedtuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines == ["NT(a=1, b='b') == NT(a=1, b='c')", '', 'Omitting 1 identical items, use -vv to show', 'Differing attributes:', "['b']", '', 'Drill down into differing attribute b:', "  b: 'b' != 'c'", '  - c', '  + b', 'Use -v to get more diff']': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_comparing_two_different_namedtuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines == ["NT1(a=1, b='b') == NT2(a=2, b='b')", '', 'At index 0 diff: 1 != 2', 'Use -v to get more diff']': Unknown symbol: lines
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_special_chars_full
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == 'assert foo'': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_where
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_and
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_where_nested
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_newline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_newline_escaped
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_newline_before_where
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_fmt_multi_newline_before_where
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'util.format_explanation(expl) == res': Unsupported AST node: Call(func=Attribute(value=Name(id='util', ctx=Load()), attr='format_explanation', ctx=Load()), args=[Name(id='expl', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_doesnt_truncate_when_input_is_empty_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_doesnt_truncate_at_when_input_is_5_lines_and_LT_max_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_8_lines_when_given_list_of_empty_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(result) != len(expl)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='result', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_8_lines_when_first_8_lines_are_LT_max_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result != expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_8_lines_when_there_is_one_line_to_remove
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_edgecase_when_truncation_message_makes_the_result_longer_for_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == [line, line]': Unsupported AST node: List(elts=[Name(id='line', ctx=Load()), Name(id='line', ctx=Load())], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_edgecase_when_truncation_message_makes_the_result_longer_for_lines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == [line, line]': Unsupported AST node: List(elts=[Name(id='line', ctx=Load()), Name(id='line', ctx=Load())], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_8_lines_when_first_8_lines_are_EQ_max_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result != expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_4_lines_when_first_4_lines_are_GT_max_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result != expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertion.py
FUNCTION: test_truncates_at_1_line_when_first_line_is_GT_max_chars
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result != expl': Unknown symbol: expl
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_resolve_package_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_package_path(pkg) == pkg': Unsupported AST node: Call(func=Name(id='resolve_package_path', ctx=Load()), args=[Name(id='pkg', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_package_unimportable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_package_path(subdir) == subdir': Unsupported AST node: Call(func=Name(id='resolve_package_path', ctx=Load()), args=[Name(id='subdir', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_access_denied_during_cleanup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not lock_path.is_file()': Unsupported AST node: Call(func=Attribute(value=Name(id='lock_path', ctx=Load()), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_long_path_during_cleanup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.path.isdir(extended_path)': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='path', ctx=Load()), attr='isdir', ctx=Load()), args=[Name(id='extended_path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_get_extended_length_path_str
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_extended_length_path_str('c:\\foo') == '\\\\?\\c:\\foo'': Unsupported AST node: Call(func=Name(id='get_extended_length_path_str', ctx=Load()), args=[Constant(value='c:\\foo')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_suppress_error_removing_lock
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lock.is_file()': Unsupported AST node: Call(func=Attribute(value=Name(id='lock', ctx=Load()), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_bestrelpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'bestrelpath(curdir, curdir) == '.'': Unsupported AST node: Call(func=Name(id='bestrelpath', ctx=Load()), args=[Name(id='curdir', ctx=Load()), Name(id='curdir', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_commonpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'commonpath(path, subpath) == path': Unsupported AST node: Call(func=Name(id='commonpath', ctx=Load()), args=[Name(id='path', ctx=Load()), Name(id='subpath', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_visit_ignores_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[entry.name for entry in visit(str(tmp_path), recurse=lambda entry: False)] == ['bar', 'foo']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='entry', ctx=Load()), attr='name', ctx=Load()), generators=[comprehension(target=Name(id='entry', ctx=Store()), iter=Call(func=Name(id='visit', ctx=Load()), args=[Call(func=Name(id='str', ctx=Load()), args=[Name(id='tmp_path', ctx=Load())], keywords=[])], keywords=[keyword(arg='recurse', value=Lambda(args=arguments(posonlyargs=[], args=[arg(arg='entry')], kwonlyargs=[], kw_defaults=[], defaults=[]), body=Constant(value=False)))]), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_samefile_false_negatives
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(module, 'foo')() == 42': Unsupported AST node: Call(func=Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='module', ctx=Load()), Constant(value='foo')], keywords=[]), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_scandir_with_non_existent_directory
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == []': Unsupported AST node: List(elts=[], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_safe_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'safe_exists(d) is True': Unsupported AST node: Call(func=Name(id='safe_exists', ctx=Load()), args=[Name(id='d', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_sets_module_as_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'baz.__name__ == 'foo.bar.baz'': Unsupported AST node: Attribute(value=Name(id='baz', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_sets_module_as_attribute_without_init_files
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'baz.__name__ == 'foo.bar.baz'': Unsupported AST node: Attribute(value=Name(id='baz', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_sets_module_as_attribute_regression
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_submodule_not_namespace
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'foo.__name__ == 'foo'': Unsupported AST node: Attribute(value=Name(id='foo', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_ns_import_same_name_directory_12592
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_is_importable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'is_importable('bar.foo', path) is True': Unsupported AST node: Call(func=Name(id='is_importable', ctx=Load()), args=[Constant(value='bar.foo'), Name(id='path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_compute_module_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'compute_module_name(tmp_path, tmp_path) is None': Unsupported AST node: Call(func=Name(id='compute_module_name', ctx=Load()), args=[Name(id='tmp_path', ctx=Load()), Name(id='tmp_path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_matching
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fnmatch_ex(pattern, path)': Unsupported AST node: Call(func=Name(id='fnmatch_ex', ctx=Load()), args=[Name(id='pattern', ctx=Load()), Name(id='path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_matching_abspath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fnmatch_ex('tests/foo.py', abspath)': Unsupported AST node: Call(func=Name(id='fnmatch_ex', ctx=Load()), args=[Constant(value='tests/foo.py'), Name(id='abspath', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_not_matching
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not fnmatch_ex(pattern, path)': Unsupported AST node: Call(func=Name(id='fnmatch_ex', ctx=Load()), args=[Name(id='pattern', ctx=Load()), Name(id='path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: path1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path.joinpath('samplefile').exists()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path', ctx=Load()), attr='joinpath', ctx=Load()), args=[Constant(value='samplefile')], keywords=[]), attr='exists', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_smoke_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obj.x == 42': Unsupported AST node: Attribute(value=Name(id='obj', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_messy_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module.__name__ == 'foo__init__'': Unsupported AST node: Attribute(value=Name(id='module', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'm.__name__ == 'hello_123'': Unsupported AST node: Attribute(value=Name(id='m', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_a
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.result == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='result', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_b
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.stuff == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='stuff', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_c
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.value == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='value', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_d
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.value2 == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='value2', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_after
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod1.__name__ == 'xxxpackage.module1'': Unsupported AST node: Attribute(value=Name(id='mod1', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_check_filepath_consistency
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'modname == name': Unknown symbol: modname
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_ensuresyspath_append
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(root1) not in sys.path': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='root1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_importmode_importlib
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module.foo(2) == 42': Unsupported AST node: Call(func=Attribute(value=Name(id='module', ctx=Load()), attr='foo', ctx=Load()), args=[Constant(value=2)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_remembers_previous_imports
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module1 is module2': Unknown symbol: module1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_no_meta_path_found
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module.foo(2) == 42': Unsupported AST node: Call(func=Attribute(value=Name(id='module', ctx=Load()), attr='foo', ctx=Load()), args=[Constant(value=2)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_importmode_importlib_with_dataclass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'data.value == 'foo'': Unsupported AST node: Attribute(value=Name(id='data', ctx=Load()), attr='value', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_importmode_importlib_with_pickle
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'action() == 42': Unsupported AST node: Call(func=Name(id='action', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_importmode_importlib_with_pickle_separate_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'round_trip(Data1(20)) == Data1(20)': Unsupported AST node: Call(func=Name(id='round_trip', ctx=Load()), args=[Call(func=Name(id='Data1', ctx=Load()), args=[Constant(value=20)], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_module_name_from_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == 'src.tests.test_foo'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_resolve_pkg_root_and_module_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'resolve_pkg_root_and_module_name(models_py, consider_namespace_packages=True) == (tmp_path / 'src', 'app.core.models')': Unsupported AST node: Call(func=Name(id='resolve_pkg_root_and_module_name', ctx=Load()), args=[Name(id='models_py', ctx=Load())], keywords=[keyword(arg='consider_namespace_packages', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_insert_missing_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sorted(modules) == ['xxx', 'xxx.tests', 'xxx.tests.foo']': Unsupported AST node: Call(func=Name(id='sorted', ctx=Load()), args=[Name(id='modules', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_module_using_spec
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod is not None': Unknown symbol: mod
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_parent_contains_child_module_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sorted(modules) == ['xxx', 'xxx.tests', 'xxx.tests.foo']': Unsupported AST node: Call(func=Name(id='sorted', ctx=Load()), args=[Name(id='modules', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_importlib_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(mod.instance.INSTANCES) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='mod', ctx=Load()), attr='instance', ctx=Load()), attr='INSTANCES', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: create_installed_doctests_and_tests_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(site_packages / 'app/core.py').is_file()': Unsupported AST node: Call(func=Attribute(value=BinOp(left=Name(id='site_packages', ctx=Load()), op=Div(), right=Constant(value='app/core.py')), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_using_normal_mechanism_first
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.__name__ == 'app.core'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_import_path_imports_correct_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.__file__ and Path(mod.__file__) == x_in_sub_folder': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='__file__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: setup_directories
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'r.ret == 0': Unsupported AST node: Attribute(value=Name(id='r', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_resolve_pkg_root_and_module_name_ns_multiple_levels
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(pkg_root, module_name) == (tmp_path / 'src/dist1', 'com.company.app.core.models')': Unsupported AST node: Tuple(elts=[Name(id='pkg_root', ctx=Load()), Name(id='module_name', ctx=Load())], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_ns_multiple_levels_import_rewrite_assertions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(pkg_root, module_name) == (tmp_path / 'src/dist2', 'com.company.calc.algo.test_demo')': Unsupported AST node: Tuple(elts=[Name(id='pkg_root', ctx=Load()), Name(id='module_name', ctx=Load())], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_ns_multiple_levels_import_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_incorrect_namespace_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'r.ret == 1': Unsupported AST node: Attribute(value=Name(id='r', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_detect_meta_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(pkg_root, module_name) == (tmp_path / 'src/dist1/com/company', 'app.core.models')': Unsupported AST node: Tuple(elts=[Name(id='pkg_root', ctx=Load()), Name(id='module_name', ctx=Load())], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pathlib.py
FUNCTION: test_full_ns_packages_without_init_files
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'r.ret == 0': Unsupported AST node: Attribute(value=Name(id='r', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_collect_imported_tests.py
FUNCTION: test_collect_imports_disabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[x.nodeid for x in reports] == ['', 'tests/foo_test.py::TestDomain', 'tests/foo_test.py', 'tests']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='nodeid', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Name(id='reports', ctx=Load()), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_one_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_two_dirs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_local_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_module_not_found
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_no_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_python_path.py
FUNCTION: test_clean_up
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/conftest.py
FUNCTION: get_write_msg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.lines[idx][0] == TWMock.WRITE': Unsupported AST node: Subscript(value=Subscript(value=Attribute(value=Name(id='self', ctx=Load()), attr='lines', ctx=Load()), slice=Name(id='idx', ctx=Load()), ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_entry_points.py
FUNCTION: test_pytest_entry_points_are_identical
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'entry_map['pytest'].value == entry_map['py.test'].value': Unsupported AST node: Attribute(value=Subscript(value=Name(id='entry_map', ctx=Load()), slice=Constant(value='pytest'), ctx=Load()), attr='value', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_link_resolve.py
FUNCTION: subst_path_windows
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.path.exists(drive)': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='path', ctx=Load()), attr='exists', ctx=Load()), args=[Name(id='drive', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_scope.py
FUNCTION: test_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Scope.Session > Scope.Package': Unsupported AST node: Attribute(value=Name(id='Scope', ctx=Load()), attr='Session', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_scope.py
FUNCTION: test_next_lower
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Scope.Session.next_lower() is Scope.Package': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='Scope', ctx=Load()), attr='Session', ctx=Load()), attr='next_lower', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_scope.py
FUNCTION: test_next_higher
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Scope.Function.next_higher() is Scope.Class': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='Scope', ctx=Load()), attr='Function', ctx=Load()), attr='next_higher', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_scope.py
FUNCTION: test_from_user
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Scope.from_user('module', 'for parametrize', 'some::id') is Scope.Module': Unsupported AST node: Call(func=Attribute(value=Name(id='Scope', ctx=Load()), attr='from_user', ctx=Load()), args=[Constant(value='module'), Constant(value='for parametrize'), Constant(value='some::id')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_importplugin_error_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(excinfo.value).endswith('Error importing plugin "qwe": Not possible to import: ☺')': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load())], keywords=[]), attr='endswith', ctx=Load()), args=[Constant(value='Error importing plugin "qwe": Not possible to import: ☺')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_addhooks_conftestplugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res == [11]': Unknown symbol: res
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_addhooks_nohooks
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret != 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_do_option_postinitialize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not hasattr(config.option, 'test123')': Unsupported AST node: Call(func=Name(id='hasattr', ctx=Load()), args=[Attribute(value=Name(id='config', ctx=Load()), attr='option', ctx=Load()), Constant(value='test123')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_configure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_conftestpath_case_sensitivity
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'plugin is mod': Unknown symbol: plugin
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_hook_proxy
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ihook_a is not None': Unknown symbol: ihook_a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_register_imported_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pm.is_registered(mod)': Unsupported AST node: Call(func=Attribute(value=Name(id='pm', ctx=Load()), attr='is_registered', ctx=Load()), args=[Name(id='mod', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_canonical_import
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pm.get_plugin('pytest_xyz') == mod': Unsupported AST node: Call(func=Attribute(value=Name(id='pm', ctx=Load()), attr='get_plugin', ctx=Load()), args=[Constant(value='pytest_xyz')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_consider_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p1 is not None': Unknown symbol: p1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_consider_module_import_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'call.plugin.__name__ == 'pytest_a'': Unsupported AST node: Attribute(value=Attribute(value=Name(id='call', ctx=Load()), attr='plugin', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_plugin_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_consider_env_plugin_instantiation
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'l2 == l1 + 1': Unknown symbol: l2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_pluginmanager_ENV_startup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_import_plugin_importname
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len1 == len2': Unknown symbol: len1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_import_plugin_dotted_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod is not None': Unknown symbol: mod
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_preparse_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''"hello123"' in excinfo.value.args[0]': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_plugin_prevent_register
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(l2) == len(l1)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='l2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_plugin_prevent_register_unregistered_already_registered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '42 in l1': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_plugin_prevent_register_stepwise_on_cacheprovider_unregister
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '42 in l1': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pluginmanager.py
FUNCTION: test_blocked_plugin_can_be_used
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytestpm.has_plugin('abc')': Unsupported AST node: Call(func=Attribute(value=Name(id='pytestpm', ctx=Load()), attr='has_plugin', ctx=Load()), args=[Constant(value='abc')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: assert_attr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'on_node == expected': Unknown symbol: on_node
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_mangle_test_address
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newnames == ['a.my.py.thing', 'Class', 'method', '[a-1-::]']': Unknown symbol: newnames
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_dont_configure_on_workers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(gotten) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='gotten', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_nullbyte
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''\x00' not in text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_logxml_path_expansion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'xml_tilde.logfile == str(home_tilde)': Unsupported AST node: Attribute(value=Name(id='xml_tilde', ctx=Load()), attr='logfile', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_logxml_changingdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_logxml_makedir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_escaped_parametrized_names_xml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_double_colon_split_function_issue469
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_double_colon_split_method_issue469
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_record_fixtures_without_junitxml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_random_report_log_xdist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == ['test_x[22]']': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_root_testsuites_tag
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'root.tag == 'testsuites'': Unsupported AST node: Attribute(value=Name(id='root', ctx=Load()), attr='tag', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_runs_twice
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'first == second': Unknown symbol: first
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_runs_twice_xdist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'first == second': Unknown symbol: first
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_fancy_items_regression
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'items == ['conftest a', 'conftest a', 'conftest b', 'test_fancy_items_regression a', 'test_fancy_items_regression a', 'test_fancy_items_regression b', 'test_fancy_items_regression test_pass']': Unknown symbol: items
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_global_properties
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'properties.length == 1': Unsupported AST node: Attribute(value=Name(id='properties', ctx=Load()), attr='length', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_url_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'test_case.getAttribute('url') == test_url': Unsupported AST node: Call(func=Attribute(value=Name(id='test_case', ctx=Load()), attr='getAttribute', ctx=Load()), args=[Constant(value='url')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_record_testsuite_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_record_testsuite_property_junit_disabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_record_testsuite_property_type_checking
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_set_suite_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_escaped_skipreason_issue3533
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''1 <> 2' in snode.text': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_bin_escaped_skipreason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''#x1B[31;1mred#x1B[0m' in snode.text': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_escaped_setup_teardown_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''#x1B[31mred#x1B[m' in snode['message']': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_logging_passing_tests_disabled_does_not_log_test_output
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_logging_passing_tests_disabled_logs_output_for_failing_test_issue5430
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: get_unique_child
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(children) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='children', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(text, minidom.Text)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='text', ctx=Load()), Attribute(value=Name(id='minidom', ctx=Load()), attr='Text', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_uc_root
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'document.get_unique_child.tag == 'root'': Unsupported AST node: Attribute(value=Attribute(value=Name(id='document', ctx=Load()), attr='get_unique_child', ctx=Load()), attr='tag', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_node_getitem
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'item['name'] == 'a'': Unsupported AST node: Subscript(value=Name(id='item', ctx=Load()), slice=Constant(value='name'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_node_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(item) == item.toxml()': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Name(id='item', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_summing_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_summing_simple_with_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_timestamp_in_xml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'start_time <= timestamp < datetime.now(timezone.utc)': Unknown symbol: start_time
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_timing_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'val is not None': Unknown symbol: val
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_setup_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_teardown_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_call_failure_teardown_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_skip_contains_name_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_mark_skip_contains_name_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_mark_skipif_contains_name_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_mark_skip_doesnt_capture_output
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_classname_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_classname_nested_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_internal_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_failure_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_failure_escape
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_junit_prefixing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_xfailure_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_xfailure_marker
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_xfail_captures_output_once
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(tnode.find_by_tag('system-err')) == expected_err_output_len': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Call(func=Attribute(value=Name(id='tnode', ctx=Load()), attr='find_by_tag', ctx=Load()), args=[Constant(value='system-err')], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_collect_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_junitxml.py
FUNCTION: test_summing_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_report_extra_parameters
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'report.newthing == 1': Unsupported AST node: Attribute(value=Name(id='report', ctx=Load()), attr='newthing', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_callinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ci.when == 'collect'': Unsupported AST node: Attribute(value=Name(id='ci', ctx=Load()), attr='when', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_outcomeexception_exceptionattributes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'outcome.args[0] == outcome.msg': Unsupported AST node: Subscript(value=Attribute(value=Name(id='outcome', ctx=Load()), attr='args', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_exit
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.errisinstance(pytest.exit.Exception)': Unsupported AST node: Call(func=Attribute(value=Name(id='excinfo', ctx=Load()), attr='errisinstance', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='pytest', ctx=Load()), attr='exit', ctx=Load()), attr='Exception', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's.startswith('Failed')': Unsupported AST node: Call(func=Attribute(value=Name(id='s', ctx=Load()), attr='startswith', ctx=Load()), args=[Constant(value='Failed')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_exit_returncode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strip_resource_warnings(result.stderr.lines) == []': Unsupported AST node: Call(func=Name(id='_strip_resource_warnings', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_no_tests_collected_exit_status
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_exception_printing_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytest.skip.Exception == pytest.skip.Exception': Unsupported AST node: Attribute(value=Attribute(value=Name(id='pytest', ctx=Load()), attr='skip', ctx=Load()), attr='Exception', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_importorskip_imports_last_module_part
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.path == ospath': Unsupported AST node: Attribute(value=Name(id='os', ctx=Load()), attr='path', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_cmdline_main
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ret == 0': Unknown symbol: ret
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_unicode_in_longrepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_store_except_info_on_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys.last_type is IndexError': Unsupported AST node: Attribute(value=Name(id='sys', ctx=Load()), attr='last_type', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_current_test_env_var
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_outcome_exception_bad_msg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(excinfo.value) == expected': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_pytest_version_env_var
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_teardown_multiple_one_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'err.value.args == ('oops',)': Unsupported AST node: Attribute(value=Attribute(value=Name(id='err', ctx=Load()), attr='value', ctx=Load()), attr='args', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_teardown_multiple_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'err1.args == ('oops1',)': Unsupported AST node: Attribute(value=Name(id='err1', ctx=Load()), attr='args', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_teardown_multiple_scopes_one_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'module_teardown == ['fin_module']': Unknown symbol: module_teardown
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_teardown_multiple_scopes_several_fail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(mod, KeyError)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='mod', ctx=Load()), Name(id='KeyError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_cached_exception_doesnt_get_longer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_passfunction
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.passed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='passed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_failfunction
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.passed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='passed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_skipfunction
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_skip_in_setup_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_failure_in_setup_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.skipped': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='skipped', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_failure_in_teardown_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_custom_failure_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.skipped': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='skipped', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_teardown_final_returncode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rec.ret == 1': Unsupported AST node: Attribute(value=Name(id='rec', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_logstart_logfinish_hooks
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[x._name for x in reps] == ['pytest_runtest_logstart', 'pytest_runtest_logfinish']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='_name', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Name(id='reps', ctx=Load()), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_exact_teardown_issue90
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reps[2].when == 'teardown'': Unsupported AST node: Attribute(value=Subscript(value=Name(id='reps', ctx=Load()), slice=Constant(value=2), ctx=Load()), attr='when', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_exact_teardown_issue1206
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reps) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reps', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_failure_in_setup_function_ignores_custom_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_systemexit_does_not_bail_out
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_collect_result
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rep.failed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: raise_assertion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_no_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'captured == []': Unknown symbol: captured
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_import_error_with_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'warning.category is pytest.PytestDeprecationWarning': Unsupported AST node: Attribute(value=Name(id='warning', ctx=Load()), attr='category', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_import_error_suppress_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'captured == []': Unknown symbol: captured
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_longreprtext_pass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.longreprtext == ''': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='longreprtext', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_longreprtext_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(call_rep.longrepr, tuple)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='call_rep', ctx=Load()), attr='longrepr', ctx=Load()), Name(id='tuple', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_longreprtext_collect_skip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(call.report.longrepr, tuple)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Attribute(value=Name(id='call', ctx=Load()), attr='report', ctx=Load()), attr='longrepr', ctx=Load()), Name(id='tuple', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_longreprtext_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''assert 1 == 4' in rep.longreprtext': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_captured_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'setup.capstdout == 'setup: stdout\n'': Unsupported AST node: Attribute(value=Name(id='setup', ctx=Load()), attr='capstdout', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_no_captured_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.capstdout == ''': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='capstdout', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner.py
FUNCTION: test_longrepr_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(rep.longrepr, ExceptionChainRepr)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Attribute(value=Name(id='rep', ctx=Load()), attr='longrepr', ctx=Load()), Name(id='ExceptionChainRepr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_preparse_ordering_with_setuptools
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'plugin.x == 42': Unsupported AST node: Attribute(value=Name(id='plugin', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_disable_plugin_autoload
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'has_loaded == (bool(enable_plugin_method) or not disable_plugin_method)': Unknown symbol: has_loaded
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_plugin_loading_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_toolongargs_issue224
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_in_subdirectory_colon_command_line_issue2148
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_notify_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''ValueError' in err': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_no_terminal_discovery_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_load_initial_conftest_last_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'hookimpls == [('_pytest.config', 'nonwrapper'), (m.__module__, 'nonwrapper'), ('_pytest.legacypath', 'nonwrapper'), ('_pytest.capture', 'wrapper'), ('_pytest.warnings', 'wrapper')]': Unknown symbol: hookimpls
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_get_plugin_specs_as_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_get_plugin_specs_as_list(None) == []': Unsupported AST node: Call(func=Name(id='_get_plugin_specs_as_list', ctx=Load()), args=[Constant(value=None)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_collect_pytest_prefix_bug
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pm.parse_hookimpl_opts(Dummy(), 'pytest_something') is None': Unsupported AST node: Call(func=Attribute(value=Name(id='pm', ctx=Load()), attr='parse_hookimpl_opts', ctx=Load()), args=[Call(func=Name(id='Dummy', ctx=Load()), args=[], keywords=[]), Constant(value='pytest_something')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_help_via_addopts
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_help_and_version_after_argument_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''to see available markers type: pytest --markers' not in result.stdout.lines': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_help_formatter_uses_py_get_terminal_width
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'formatter._width == 90': Unsupported AST node: Attribute(value=Name(id='formatter', ctx=Load()), attr='_width', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_does_not_load_blocked_plugin_from_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_invocation_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(calls) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_blocked_default_plugins
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_strtobool
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_strtobool('YES')': Unsupported AST node: Call(func=Name(id='_strtobool', ctx=Load()), args=[Constant(value='YES')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_parse_warning_filter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'parse_warning_filter(arg, escape=escape) == expected': Unsupported AST node: Call(func=Name(id='parse_warning_filter', ctx=Load()), args=[Name(id='arg', ctx=Load())], keywords=[keyword(arg='escape', value=Name(id='escape', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_getcfg_and_config
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cfg['name'] == 'value'': Unsupported AST node: Subscript(value=Name(id='cfg', ctx=Load()), slice=Constant(value='name'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_setupcfg_uses_toolpytest_with_pytest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_append_parse_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.option.color == 'no'': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='option', ctx=Load()), attr='color', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_tox_ini_wrong_version
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_ini_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('minversion') == '3.36'': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='minversion')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pyproject_toml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.inipath == pyproject_toml': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='inipath', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_empty_pyproject_toml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.inipath == pyproject_toml': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='inipath', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_empty_pyproject_toml_found_many
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.inipath == pytester.path / 'foo/bar/pyproject.toml'': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='inipath', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytest_ini_trumps_pyproject_toml
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.inipath == pytest_ini': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='inipath', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_toxini_before_lower_pytestini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('minversion') == '2.0'': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='minversion')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_ini_parse_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_toml_parse_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_confcutdir_default_without_configfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.pluginmanager._confcutdir == sub': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='pluginmanager', ctx=Load()), attr='_confcutdir', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_confcutdir_default_with_configfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.pluginmanager._confcutdir == pytester.path': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='pluginmanager', ctx=Load()), attr='_confcutdir', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_confcutdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_invalid_config_options
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sorted(config._get_unknown_ini_keys()) == sorted(invalid_keys)': Unsupported AST node: Call(func=Name(id='sorted', ctx=Load()), args=[Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='_get_unknown_ini_keys', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_args_source_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.args_source == Config.ArgsSource.ARGS': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='args_source', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_args_source_invocation_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.args_source == Config.ArgsSource.INVOCATION_DIR': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='args_source', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_args_source_testpaths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.args_source == Config.ArgsSource.TESTPATHS': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='args_source', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_explicitly_specified_config_file_is_loaded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('custom') == '1'': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='custom')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_absolute_win32_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ret == ExitCode.OK': Unknown symbol: ret
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_trace
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_getoption_declared_option_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config_novalue.getoption('hello') is None': Unsupported AST node: Call(func=Attribute(value=Name(id='config_novalue', ctx=Load()), attr='getoption', ctx=Load()), args=[Constant(value='hello')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_getoption_undeclared_option_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getoption('x', default=1) == 1': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getoption', ctx=Load()), args=[Constant(value='x')], keywords=[keyword(arg='default', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_getoption_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getoption('hello') == 'this'': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getoption', ctx=Load()), args=[Constant(value='hello')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_config_getvalueorskip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'verbose == config.option.verbose': Unknown symbol: verbose
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_getconftest_pathlist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config._getconftest_pathlist('notexist', path=tmp_path) is None': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='_getconftest_pathlist', ctx=Load()), args=[Constant(value='notexist')], keywords=[keyword(arg='path', value=Name(id='tmp_path', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'val == 'hello'': Unknown symbol: val
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini_paths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: check_config_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ['123', '123 hello', 'this']': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: check_config_linelist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini_bool
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('strip') is bool_val': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='strip')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini_int
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('ini_param') == int_val': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='ini_param')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini_float
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('ini_param') == float_val': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='ini_param')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addinivalue_line_existing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addinivalue_line_new
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not config.getini('xy')': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='xy')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addini_default_values
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'value == []': Unknown symbol: value
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_get_ini_default_for_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_ini_default_for_type(type) == expected': Unsupported AST node: Call(func=Name(id='get_ini_default_for_type', ctx=Load()), args=[Name(id='type', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_confcutdir_check_isdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getoption('confcutdir') == str(p)': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getoption', ctx=Load()), args=[Constant(value='confcutdir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_iter_rewritable_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'list(_iter_rewritable_modules(names)) == expected': Unsupported AST node: Call(func=Name(id='list', ctx=Load()), args=[Call(func=Name(id='_iter_rewritable_modules', ctx=Load()), args=[Name(id='names', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_add_cleanup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'report == ['cleanup_first', 'raise_1', 'raise_2', 'cleanup_last']': Unknown symbol: report
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_basic_behavior
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.option.verbose == 444': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='option', ctx=Load()), attr='verbose', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_invocation_params_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.args == ['a', 'b']': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='args', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_inifilename
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.args == [str(cwd)]': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='args', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: runfiletest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 2': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_simple_noini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_common_ancestor(Path.cwd(), [tmp_path]) == tmp_path': Unsupported AST node: Call(func=Name(id='get_common_ancestor', ctx=Load()), args=[Call(func=Attribute(value=Name(id='Path', ctx=Load()), attr='cwd', ctx=Load()), args=[], keywords=[]), List(elts=[Name(id='tmp_path', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytestini_overrides_empty_other
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_setuppy_fallback
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_nothing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_specific_inifile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_explicit_config_file_sets_rootdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_arg_outside_cwd_without_inifile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_arg_outside_cwd_with_inifile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == a': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_non_dir_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_existing_file_in_subdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_config_also_in_parent_directory
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rootpath == tmp_path / 'myproject'': Unknown symbol: rootpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_override_ini_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addopts_before_initini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config._override_ini == [f'cache_dir={cache_dir}']': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='_override_ini', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addopts_from_env_not_concatenated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''error: argument -o/--override-ini: expected one argument (via PYTEST_ADDOPTS)' in excinfo.value.args[0]': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_addopts_from_ini_not_concatenated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == _pytest.config.ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_override_ini_does_not_contain_paths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config._override_ini == ['cache_dir=/cache']': Unsupported AST node: Attribute(value=Name(id='config', ctx=Load()), attr='_override_ini', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_multiple_override_ini_options
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''ERROR:' not in result.stderr.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_override_ini_without_config_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.parseoutcomes() == {'passed': 1}': Unsupported AST node: Call(func=Attribute(value=Name(id='result', ctx=Load()), attr='parseoutcomes', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytest_plugins_in_non_top_level_conftest_unsupported
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 2': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytest_plugins_in_non_top_level_conftest_unsupported_pyargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == (0 if use_pyargs else 2)': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytest_plugins_in_non_top_level_conftest_unsupported_no_top_level_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 2': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_pytest_plugins_in_non_top_level_conftest_unsupported_no_false_positives
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_without_debug_does_not_write_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not [f.name for f in pytester.path.glob('**/*.log')]': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='f', ctx=Load()), attr='name', ctx=Load()), generators=[comprehension(target=Name(id='f', ctx=Store()), iter=Call(func=Attribute(value=Attribute(value=Name(id='pytester', ctx=Load()), attr='path', ctx=Load()), attr='glob', ctx=Load()), args=[Constant(value='**/*.log')], keywords=[]), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_with_only_debug_writes_pytestdebug_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''pytestdebug.log' in [f.name for f in pytester.path.glob('**/*.log')]': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_multiple_custom_debug_logs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{'bar.log', 'foo.log'} == {f.name for f in pytester.path.glob('**/*.log')}': Unsupported AST node: Set(elts=[Constant(value='bar.log'), Constant(value='foo.log')])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_level_matches_verbose_when_not_specified
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity(TestVerbosity.SOME_OUTPUT_TYPE) == config.option.verbose': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[Attribute(value=Name(id='TestVerbosity', ctx=Load()), attr='SOME_OUTPUT_TYPE', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_level_matches_verbose_when_not_known_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity('some fake verbosity type') == config.option.verbose': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[Constant(value='some fake verbosity type')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: test_level_matches_specified_override
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.get_verbosity(TestVerbosity.SOME_OUTPUT_TYPE) == TestVerbosity.SOME_OUTPUT_VERBOSITY_LEVEL': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='get_verbosity', ctx=Load()), args=[Attribute(value=Name(id='TestVerbosity', ctx=Load()), attr='SOME_OUTPUT_TYPE', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_config.py
FUNCTION: __getattr__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'name in ('__loader__', '__spec__')': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_failed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(pastebinlist) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='pastebinlist', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_all
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprec.countoutcomes() == [1, 1, 1]': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='countoutcomes', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_non_ascii_paste_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(pastebinlist) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='pastebinlist', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_pastebin_invalid_url
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == 'bad response: invalid format (\'View <a href="/invalid/3c0c6750bd">raw</a>.\')'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_pastebin_http_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == 'bad response: HTTP Error 400: Bad request'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_pastebin_url_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == 'bad response: <urlopen error the url was bad>'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_create_new_paste
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == 'https://bpa.st/show/3c0c6750bd'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pastebin.py
FUNCTION: test_create_new_paste_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == "bad response: invalid format ('something bad occurred')"': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_get_dirs_from_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_dirs_from_args([str(fn), str(tmp_path / 'does_not_exist'), str(d), option, xdist_rsync_option]) == [fn.parent, d]': Unsupported AST node: Call(func=Name(id='get_dirs_from_args', ctx=Load()), args=[List(elts=[Call(func=Name(id='str', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[]), Call(func=Name(id='str', ctx=Load()), args=[BinOp(left=Name(id='tmp_path', ctx=Load()), op=Div(), right=Constant(value='does_not_exist'))], keywords=[]), Call(func=Name(id='str', ctx=Load()), args=[Name(id='d', ctx=Load())], keywords=[]), Name(id='option', ctx=Load()), Name(id='xdist_rsync_option', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_is_fs_root
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'is_fs_root(Path(path)) is expected': Unsupported AST node: Call(func=Name(id='is_fs_root', ctx=Load()), args=[Call(func=Name(id='Path', ctx=Load()), args=[Name(id='path', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_empty_pytest_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) == {}': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_pytest_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) == {'x': '1'}': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_custom_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) == {'x': '1'}': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_custom_ini_without_section
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) is None': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_custom_cfg_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) is None': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_valid_cfg_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) == {'x': '1'}': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_custom_toml_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) is None': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_valid_toml_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'load_config_dict_from_file(fn) == {'x': '1', 'y': '20.0', 'values': ['tests', 'integration'], 'name': 'foo', 'heterogeneous_array': [1, 'str']}': Unsupported AST node: Call(func=Name(id='load_config_dict_from_file', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_has_ancestor
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_common_ancestor(cwd, [fn1, fn2]) == tmp_path / 'foo'': Unsupported AST node: Call(func=Name(id='get_common_ancestor', ctx=Load()), args=[Name(id='cwd', ctx=Load()), List(elts=[Name(id='fn1', ctx=Load()), Name(id='fn2', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_single_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_common_ancestor(Path.cwd(), [tmp_path]) == tmp_path': Unsupported AST node: Call(func=Name(id='get_common_ancestor', ctx=Load()), args=[Call(func=Attribute(value=Name(id='Path', ctx=Load()), attr='cwd', ctx=Load()), args=[], keywords=[]), List(elts=[Name(id='tmp_path', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_findpaths.py
FUNCTION: test_single_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_common_ancestor(Path.cwd(), [fn]) == tmp_path': Unsupported AST node: Call(func=Name(id='get_common_ancestor', ctx=Load()), args=[Call(func=Attribute(value=Name(id='Path', ctx=Load()), attr='cwd', ctx=Load()), args=[], keywords=[]), List(elts=[Name(id='fn', ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_error_diffs.py
FUNCTION: test_error_diff
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_strict_prohibits_unregistered_markers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_option
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed_str == expected_passed': Unknown symbol: passed_str
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_option_with_kwargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed_str == expected_passed': Unknown symbol: passed_str
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_option_custom
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed_str == expected_passed': Unknown symbol: passed_str
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_option_custom
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed_str == expected_passed': Unknown symbol: passed_str
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_option_considers_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(passed) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_option_parametrize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed_str == expected_passed': Unknown symbol: passed_str
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_parametrize_with_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed[0].nodeid.split('::')[-1] == expected_id': Unsupported AST node: Subscript(value=Call(func=Attribute(value=Attribute(value=Subscript(value=Name(id='passed', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='nodeid', ctx=Load()), attr='split', ctx=Load()), args=[Constant(value='::')], keywords=[]), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_option_wrong_arguments
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'expected_error in err': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_parametrized_with_kwargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_parametrize_iterator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_parameterset_for_parametrize_marks
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result_mark.name == mark': Unsupported AST node: Attribute(value=Name(id='result_mark', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_parameterset_for_fail_at_collect
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.INTERRUPTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_expressions_no_smear
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed == 1': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_addmarker_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'extracted == ['baz', 'foo', 'bar']': Unknown symbol: extracted
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_pytest_param_id_requires_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg == expected': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_pytest_param_id_allows_none_or_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytest.param(id=s)': Unsupported AST node: Call(func=Attribute(value=Name(id='pytest', ctx=Load()), attr='param', ctx=Load()), args=[], keywords=[keyword(arg='id', value=Name(id='s', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_marker_expr_eval_failure_handling
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_mro
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'all_marks == [xfail('b').mark, xfail('a').mark, xfail('c').mark]': Unknown symbol: all_marks
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_pytest_exists_in_namespace_all
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'attr in module.__all__': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_with_param
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytest.mark.foo(some_function) is some_function': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='pytest', ctx=Load()), attr='mark', ctx=Load()), attr='foo', ctx=Load()), args=[Name(id='some_function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_should_not_pass_to_siebling_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not list(base_item.iter_markers(name='b'))': Unsupported AST node: Call(func=Name(id='list', ctx=Load()), args=[Call(func=Attribute(value=Name(id='base_item', ctx=Load()), attr='iter_markers', ctx=Load()), args=[], keywords=[keyword(arg='name', value=Constant(value='b'))])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_closest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'has_own_marker is not None': Unknown symbol: has_own_marker
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_mark_with_wrong_marker
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_no_marker_match_on_unmarked_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(passed) + len(skipped) + len(failed) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_select_extra_keywords
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(passed) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_extra
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'failed == 1': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_keyword_extra_dash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed + skipped + failed == 0': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_no_magic_values
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'passed + skipped + failed == 0': Unknown symbol: passed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_no_match_directories_outside_the_suite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_collected_names() == ['test_aaa', 'test_ddd']': Unsupported AST node: Call(func=Name(id='get_collected_names', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: test_aliases
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'md.name == 'foo'': Unsupported AST node: Attribute(value=Name(id='md', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: check
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(failed) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='failed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_mark.py
FUNCTION: get_collected_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(calls) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_get_user_uid_not_found
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_user() is None': Unsupported AST node: Call(func=Name(id='get_user', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_get_user
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_user() is None': Unsupported AST node: Call(func=Name(id='get_user', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_basetemp_with_read_only_files
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_tmp_path_factory_handles_invalid_dir_characters
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''pytest-of-unknown' in str(p)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_tmp_path_factory_create_directory_with_safe_permissions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'basetemp.stat().st_mode & 63 == 0': Unsupported binary op: <class 'ast.BitAnd'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_tmp_path_factory_fixes_up_world_readable_permissions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'basetemp.parent.stat().st_mode & 63 != 0': Unsupported binary op: <class 'ast.BitAnd'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_mktemp
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(tmp.relative_to(t.getbasetemp())) == 'world0'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Attribute(value=Name(id='tmp', ctx=Load()), attr='relative_to', ctx=Load()), args=[Call(func=Attribute(value=Name(id='t', ctx=Load()), attr='getbasetemp', ctx=Load()), args=[], keywords=[])], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_tmppath_relative_basetemp_absolute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't.getbasetemp().resolve() == (tmp_path / 'hello').resolve()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='t', ctx=Load()), attr='getbasetemp', ctx=Load()), args=[], keywords=[]), attr='resolve', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_getbasetemp_custom_removes_old
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mytemp.exists()': Unsupported AST node: Call(func=Attribute(value=Name(id='mytemp', ctx=Load()), attr='exists', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_lock_register_cleanup_removal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lock.is_file()': Unsupported AST node: Call(func=Attribute(value=Name(id='lock', ctx=Load()), attr='is_file', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_cleanup_keep_0
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'dir_num == 0': Unknown symbol: dir_num
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_cleanup_locked
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not pathlib.ensure_deletable(p, consider_lock_dead_if_created_before=p.stat().st_mtime - 1)': Unsupported AST node: Call(func=Attribute(value=Name(id='pathlib', ctx=Load()), attr='ensure_deletable', ctx=Load()), args=[Name(id='p', ctx=Load())], keywords=[keyword(arg='consider_lock_dead_if_created_before', value=BinOp(left=Attribute(value=Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='stat', ctx=Load()), args=[], keywords=[]), attr='st_mtime', ctx=Load()), op=Sub(), right=Constant(value=1)))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_removal_accepts_lock
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'folder.is_dir()': Unsupported AST node: Call(func=Attribute(value=Name(id='folder', ctx=Load()), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_rm_rf
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not adir.exists()': Unsupported AST node: Call(func=Attribute(value=Name(id='adir', ctx=Load()), attr='exists', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_rm_rf_with_read_only_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not fn.parent.is_dir()': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='fn', ctx=Load()), attr='parent', ctx=Load()), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_rm_rf_with_read_only_directory
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not adir.is_dir()': Unsupported AST node: Call(func=Attribute(value=Name(id='adir', ctx=Load()), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_tmpdir.py
FUNCTION: test_on_rm_rf_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not on_rm_rf_error(None, str(fn), exc_info2, start_path=tmp_path)': Unsupported AST node: Call(func=Name(id='on_rm_rf_error', ctx=Load()), args=[Constant(value=None), Call(func=Name(id='str', ctx=Load()), args=[Name(id='fn', ctx=Load())], keywords=[]), Name(id='exc_info2', ctx=Load())], keywords=[keyword(arg='start_path', value=Name(id='tmp_path', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable_in_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable_in_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable_warning_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable_warning_multiple_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_unraisable_collection_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_refcycle_unraisable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_refcycle_unraisable_warning_filter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_create_task_raises_unraisable_warning_filter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_refcycle_unraisable_warning_filter_default
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_unraisableexception.py
FUNCTION: test_possibly_none_excinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner_xunit.py
FUNCTION: test_module_and_function_setup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rep.passed': Unsupported AST node: Attribute(value=Name(id='rep', ctx=Load()), attr='passed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner_xunit.py
FUNCTION: test_module_setup_failure_no_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'calls[0].item.module.values == [1]': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Subscript(value=Name(id='calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='item', ctx=Load()), attr='module', ctx=Load()), attr='values', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner_xunit.py
FUNCTION: test_setup_function_failure_no_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'calls[0].item.module.modlevel == [1]': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Subscript(value=Name(id='calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='item', ctx=Load()), attr='module', ctx=Load()), attr='modlevel', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_runner_xunit.py
FUNCTION: test_setup_teardown_function_level_with_optional_argument
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'trace_setups_teardowns == expected': Unknown symbol: trace_setups_teardowns
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_ignore
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'WARNINGS_SUMMARY_HEADER not in result.stdout.str()': Unknown symbol: WARNINGS_SUMMARY_HEADER
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_filterwarnings_mark_registration
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_warning_recorded_hook
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(collected) == len(expected)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='collected', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_mark_regex_escape
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'WARNINGS_SUMMARY_HEADER not in result.stdout.str()': Unknown symbol: WARNINGS_SUMMARY_HEADER
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_pytest_configure_warning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 5': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_hidden_by_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'WARNINGS_SUMMARY_HEADER not in result.stdout.str()': Unknown symbol: WARNINGS_SUMMARY_HEADER
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_hidden_by_cmdline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'WARNINGS_SUMMARY_HEADER not in result.stdout.str()': Unknown symbol: WARNINGS_SUMMARY_HEADER
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_hidden_by_system
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'WARNINGS_SUMMARY_HEADER not in result.stdout.str()': Unknown symbol: WARNINGS_SUMMARY_HEADER
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_invalid_regex_in_filterwarning
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == pytest.ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_issue4445_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(capwarn.captured) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='capwarn', ctx=Load()), attr='captured', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_issue4445_preparse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(capwarn.captured) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='capwarn', ctx=Load()), attr='captured', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_warnings.py
FUNCTION: test_issue4445_import_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(capwarn.captured) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='capwarn', ctx=Load()), attr='captured', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_warning_on_unwrap_of_broken_object
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'inspect.unwrap.__module__ == 'inspect'': Unsupported AST node: Attribute(value=Attribute(value=Name(id='inspect', ctx=Load()), attr='unwrap', ctx=Load()), attr='__module__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_is_setup_py_not_named_setup_py
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not _is_setup_py(not_setup_py)': Unsupported AST node: Call(func=Name(id='_is_setup_py', ctx=Load()), args=[Name(id='not_setup_py', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_is_setup_py_is_a_setup_py
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_is_setup_py(setup_py)': Unsupported AST node: Call(func=Name(id='_is_setup_py', ctx=Load()), args=[Name(id='setup_py', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_is_setup_py_different_encoding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_is_setup_py(setup_py)': Unsupported AST node: Call(func=Name(id='_is_setup_py', ctx=Load()), args=[Name(id='setup_py', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_is_main_py
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_is_main_py(dunder_main) == expected': Unsupported AST node: Call(func=Name(id='_is_main_py', ctx=Load()), args=[Name(id='dunder_main', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_collect_testtextfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_multiple_patterns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{x.name for x in pytester.path.iterdir()} == expected': Unsupported AST node: SetComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='name', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Call(func=Attribute(value=Attribute(value=Name(id='pytester', ctx=Load()), attr='path', ctx=Load()), attr='iterdir', ctx=Load()), args=[], keywords=[]), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_doctest_cached_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Tacos!' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_reportinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reportinfo[1] == 1': Unsupported AST node: Subscript(value=Name(id='reportinfo', ctx=Load()), slice=Constant(value=1), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_setup_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_doctest.py
FUNCTION: test_skipping_wrapped_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''INTERNALERROR' not in result.stdout.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipped_reasons_functional
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipped_folding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_test_setup_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_item
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not failed': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_mark_xfail_item
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not failed': Unknown symbol: failed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_no_marker
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_xfail_no_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'xfailed': Unknown symbol: xfailed
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_skipif_no_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_one_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_one_arg_with_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_one_arg_twice2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_skipif_with_boolean_without_reason
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.value.msg is not None': Unsupported AST node: Attribute(value=Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load()), attr='msg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_marked_skipif_with_invalid_boolean
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.value.msg is not None': Unsupported AST node: Attribute(value=Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load()), attr='msg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'skipped': Unknown symbol: skipped
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_markeval_namespace
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 0': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_markeval_namespace_ValueError
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_xpassed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_using_platform
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_xpassed_strict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reports) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='reports', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_evalfalse_but_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'callreport.failed': Unsupported AST node: Attribute(value=Name(id='callreport', ctx=Load()), attr='failed', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_xpass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_strict_sanity
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_strict_xfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == (1 if strict else 0)': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_strict_xfail_condition
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_condition_keyword
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_strict_xfail_default_from_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == (1 if strict else 0)': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_xfail_markeval_namespace
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res.ret == 1': Unsupported AST node: Attribute(value=Name(id='res', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_conditional
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.value.msg == "condition: hasattr(os, 'sep')"': Unsupported AST node: Attribute(value=Attribute(value=Name(id='x', ctx=Load()), attr='value', ctx=Load()), attr='msg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_reporting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_skipping.py
FUNCTION: test_skipif_reporting_multiple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_make_hook_recorder
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not recorder.getfailures()': Unsupported AST node: Call(func=Attribute(value=Name(id='recorder', ctx=Load()), attr='getfailures', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_parseconfig
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config2 is not config1': Unknown symbol: config2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_with_doctest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_runresult_assertion_on_xfail
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_runresult_assertion_on_xpassed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_xpassed_with_strict_is_considered_a_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_hookrecorder_basic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'call.arg == 123': Unsupported AST node: Attribute(value=Name(id='call', ctx=Load()), attr='arg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_makepyfile_utf8
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '"mixed_encoding = 'São Paulo'".encode() in p.read_bytes()': Unsupported AST node: Call(func=Attribute(value=Constant(value="mixed_encoding = 'São Paulo'"), attr='encode', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_subprocess
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest_subprocess(testfile).ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest_subprocess', ctx=Load()), args=[Name(id='testfile', ctx=Load())], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_subprocess_via_runpytest_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_unicode_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_run_no_timeout
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest_subprocess(testfile).ret == ExitCode.OK': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest_subprocess', ctx=Load()), args=[Name(id='testfile', ctx=Load())], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_run_with_timeout
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_linematcher_with_nonlist
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lm._getlines({}) == {}': Unsupported AST node: Call(func=Attribute(value=Name(id='lm', ctx=Load()), attr='_getlines', ctx=Load()), args=[Dict(keys=[], values=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_linematcher_match_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'e.value.msg is not None': Unsupported AST node: Attribute(value=Attribute(value=Name(id='e', ctx=Load()), attr='value', ctx=Load()), attr='msg', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_linematcher_consecutive
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(excinfo.value).splitlines() == ["exact match: '1'", "no consecutive match: '2'", "   with: ''"]': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load())], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_linematcher_no_matching_after_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(e.value).splitlines() == ["fnmatch: '*'", "   with: '1'"]': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='e', ctx=Load()), attr='value', ctx=Load())], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_linematcher_string_api
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(lm) == 'foo\nbar'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='lm', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytest_addopts_before_pytester
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''PYTEST_ADDOPTS' not in os.environ': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_run_stdin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.stdout.lines == ['input', '2ndline']': Unsupported AST node: Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_popen_stdin_pipe
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stdout.decode('utf8').splitlines() == ['input', '2ndline']': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='stdout', ctx=Load()), attr='decode', ctx=Load()), args=[Constant(value='utf8')], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_popen_stdin_bytes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stdout.decode('utf8').splitlines() == ['input', '2ndline']': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='stdout', ctx=Load()), attr='decode', ctx=Load()), args=[Constant(value='utf8')], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_popen_default_stdin_stderr_and_stdin_None
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_spawn_uses_tmphome
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.environ.get('HOME') == tmphome': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='environ', ctx=Load()), attr='get', ctx=Load()), args=[Constant(value='HOME')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_run_result_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(r) == f'<RunResult ret={pytest.ExitCode.TESTS_FAILED!s} len(stdout.lines)=3 len(stderr.lines)=4 duration=0.50s>'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Name(id='r', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_outcomes_with_multiple_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.parseoutcomes() == {'errors': 2}': Unsupported AST node: Call(func=Attribute(value=Name(id='result', ctx=Load()), attr='parseoutcomes', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_parse_summary_line_always_plural
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester_mod.RunResult.parse_summary_nouns(lines) == {'errors': 1, 'failed': 1, 'passed': 1, 'warnings': 1}': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='pytester_mod', ctx=Load()), attr='RunResult', ctx=Load()), attr='parse_summary_nouns', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_makefile_joins_absolute_path
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(p1) == str(pytester.path / 'absfile.py')': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='p1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_pytester_subprocess_with_string_plugins
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_inline_run_test_module_not_cleaned_up
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_inline_run_taking_and_restoring_a_sys_modules_snapshot
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(spy_factory.instances) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='spy_factory', ctx=Load()), attr='instances', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_inline_run_sys_modules_snapshot_restore_preserving_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not spy._spy_preserve('black_knight')': Unsupported AST node: Call(func=Attribute(value=Name(id='spy', ctx=Load()), attr='_spy_preserve', ctx=Load()), args=[Constant(value='black_knight')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_external_test_module_imports_not_cleaned_up
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'imported.data == 42': Unsupported AST node: Attribute(value=Name(id='imported', ctx=Load()), attr='data', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_remove_added
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.key not in sys.modules': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='key', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_add_removed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.key not in sys.modules': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='key', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_restore_reloaded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.key not in sys.modules': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='key', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_preserve_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not any((k in sys.modules for k in key))': Unsupported AST node: Call(func=Name(id='any', ctx=Load()), args=[GeneratorExp(elt=Compare(left=Name(id='k', ctx=Load()), ops=[In()], comparators=[Attribute(value=Name(id='sys', ctx=Load()), attr='modules', ctx=Load())]), generators=[comprehension(target=Name(id='k', ctx=Store()), iter=Name(id='key', ctx=Load()), ifs=[], is_async=0)])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_preserve_container
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'self.key not in original': Unsupported AST node: Attribute(value=Name(id='self', ctx=Load()), attr='key', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_restore
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys_path == [self.path(x) for x in transformation['source']]': Unknown symbol: sys_path
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_pytester.py
FUNCTION: test_preserve_container
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getattr(sys, path_type) is new': Unsupported AST node: Call(func=Name(id='getattr', ctx=Load()), args=[Name(id='sys', ctx=Load()), Name(id='path_type', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_source_mtime_long_long
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_rewrite_infinite_recursion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'spec is not None': Unknown symbol: spec
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_get_assertion_exprs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_get_assertion_exprs(src) == expected': Unsupported AST node: Call(func=Name(id='_get_assertion_exprs', ctx=Load()), args=[Name(id='src', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_try_makedirs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'try_makedirs(p)': Unsupported AST node: Call(func=Name(id='try_makedirs', ctx=Load()), args=[Name(id='p', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_place_initial_imports
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(m.body[0], ast.Expr)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Attribute(value=Name(id='m', ctx=Load()), attr='body', ctx=Load()), slice=Constant(value=0), ctx=Load()), Attribute(value=Name(id='ast', ctx=Load()), attr='Expr', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_dont_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(m.body) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='m', ctx=Load()), attr='body', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_dont_rewrite_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''warning' not in ''.join(result.outlines)': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert False'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertrepr_compare_same_width
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_dont_rewrite_if_hasattr_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assert_already_has_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f) == 'AssertionError: something bad!\nassert False'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message_tuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message_expr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message_escape
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_messages_bytes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_message_verbosity
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_boolop
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert (False)'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_unary_op
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert not True'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_binary_op
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert (1 + -1)'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_boolop_percent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert ((3 % 2) and False)'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_call
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1, ns) == 'assert False\n +  where False = g()'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load()), Name(id='ns', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_attribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1, ns) == 'assert not 3\n +  where 3 = x.g'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load()), Name(id='ns', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_comparisons
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert 1 < 0'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg == 'assert 10 == 11\n +  where 10 = len([0, 1, 2, 3, 4, 5, ...])'': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_custom_reprcompare
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getmsg(f1) == 'assert 42'': Unsupported AST node: Call(func=Name(id='getmsg', ctx=Load()), args=[Name(id='f1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assert_raising__bool__in_comparison
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_formatchar
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_custom_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_custom_repr_non_ascii
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg is not None': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_pycache_is_a_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_zipfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_load_resource_via_files_with_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest('-vv').ret == ExitCode.OK': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[Constant(value='-vv')], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_dont_write_bytecode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest_subprocess().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest_subprocess', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_orphaned_pyc_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_cached_pyc_includes_pytest_version
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_pyc_vs_pyo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest_subprocess(tmp).ret == 1': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest_subprocess', ctx=Load()), args=[Name(id='tmp', ctx=Load())], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_package
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_translate_newlines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_package_without__init__py
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_rewrite_warning_ignore
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.stderr.str().strip()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stderr', ctx=Load()), attr='str', ctx=Load()), args=[], keywords=[]), attr='strip', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_rewrite_module_imported_from_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest_subprocess().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest_subprocess', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_remember_rewritten_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'spec is not None': Unknown symbol: spec
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_sys_meta_path_munged
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pytester.runpytest().ret == 0': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='pytester', ctx=Load()), attr='runpytest', ctx=Load()), args=[], keywords=[]), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_write_pyc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_write_pyc(state, co, os.stat(source_path), pycpath)': Unsupported AST node: Call(func=Name(id='_write_pyc', ctx=Load()), args=[Name(id='state', ctx=Load()), Name(id='co', ctx=Load()), Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='stat', ctx=Load()), args=[Name(id='source_path', ctx=Load())], keywords=[]), Name(id='pycpath', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_read_pyc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(contents) > strip_bytes': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='contents', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_read_pyc_success
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_read_pyc(fn, pyc, state.trace) is not None': Unsupported AST node: Call(func=Name(id='_read_pyc', ctx=Load()), args=[Name(id='fn', ctx=Load()), Name(id='pyc', ctx=Load()), Attribute(value=Name(id='state', ctx=Load()), attr='trace', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_read_pyc_more_invalid
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_read_pyc(source, pyc, print) is not None': Unsupported AST node: Call(func=Name(id='_read_pyc', ctx=Load()), args=[Name(id='source', ctx=Load()), Name(id='pyc', ctx=Load()), Name(id='print', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_dont_rewrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_inline_walrus_operator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_inline_walrus_operator_reverse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_no_variable_name_conflict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_true_assertion_and_changes_variable_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_fail_assertion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_boolean_composite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_compare_boolean_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_boolean_none_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_value_changes_cleared_after_each_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_in_operand
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_in_operand_json_dumps
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_equals_operand_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_equals_operand_function_keyword_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_equals_operand_function_arg_as_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_operator_gt_operand_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_assertion_walrus_different_test_cases
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: spy_write_pyc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'hook.find_spec('test_bar') is None': Unsupported AST node: Call(func=Attribute(value=Name(id='hook', ctx=Load()), attr='find_spec', ctx=Load()), args=[Constant(value='test_bar')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_basic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'hook.find_spec('conftest') is not None': Unsupported AST node: Call(func=Attribute(value=Name(id='hook', ctx=Load()), attr='find_spec', ctx=Load()), args=[Constant(value='conftest')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_option_default
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.getini('enable_assertion_pass_hook') is False': Unsupported AST node: Call(func=Attribute(value=Name(id='config', ctx=Load()), attr='getini', ctx=Load()), args=[Constant(value='enable_assertion_pass_hook')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: fake_mkdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(p, Path)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='p', ctx=Load()), Name(id='Path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_get_cache_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'get_cache_dir(Path(source)) == Path(expected)': Unsupported AST node: Call(func=Name(id='get_cache_dir', ctx=Load()), args=[Call(func=Name(id='Path', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_sys_pycache_prefix_integration
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_get_maxsize_for_saferepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_get_maxsize_for_saferepr(cast(Config, config)) == expected_size': Unsupported AST node: Call(func=Name(id='_get_maxsize_for_saferepr', ctx=Load()), args=[Call(func=Name(id='cast', ctx=Load()), args=[Name(id='Config', ctx=Load()), Name(id='config', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_get_maxsize_for_saferepr_no_config
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_get_maxsize_for_saferepr(None) == DEFAULT_REPR_MAX_SIZE': Unsupported AST node: Call(func=Name(id='_get_maxsize_for_saferepr', ctx=Load()), args=[Constant(value=None)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_constant_not_picked_as_module_docstring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_saferepr_bound_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_saferepr(self.Help().bound_method) == 'bound_method'': Unsupported AST node: Call(func=Name(id='_saferepr', ctx=Load()), args=[Attribute(value=Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='Help', ctx=Load()), args=[], keywords=[]), attr='bound_method', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: test_saferepr_unbounded
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pattern.match(_saferepr(obj))': Unsupported AST node: Call(func=Attribute(value=Name(id='pattern', ctx=Load()), attr='match', ctx=Load()), args=[Call(func=Name(id='_saferepr', ctx=Load()), args=[Name(id='obj', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: preserved
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(original_locations) > 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='original_locations', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a_global': Unknown symbol: a_global
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys == 42': Unknown symbol: sys
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f5
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cls == 42': Unknown symbol: cls
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cls().foo == 2': Unsupported AST node: Attribute(value=Call(func=Name(id='cls', ctx=Load()), args=[], keywords=[]), attr='foo', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f and g': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f and g': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f and g': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f or g': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f5
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not f and (not g)': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f6
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x() and x()': Unsupported AST node: Call(func=Name(id='x', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f7
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'False or x()': Unsupported AST node: Call(func=Name(id='x', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f8
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '1 in {} and 2 in {}': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f9
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x in {1: None} and y in {}': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f10
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f or g': Unknown symbol: f
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f11
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f() and g() and h()': Unsupported AST node: Call(func=Name(id='f', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'True or explode': Unknown symbol: explode
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == 1 or x == 2': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not x': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '~x + 1': Unsupported unary op: <class 'ast.Invert'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '-x + x': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '+x + x': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x + y': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not 5 % 4': True, False or Z3 Boolean expression expected. Received 1 of type <class 'int'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '3 % 2 and False': b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'False or 4 % 2': b'Sort mismatch at argument #1 for function (declare-fun or (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g()': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(1)': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[Constant(value=1)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(1, 2)': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[Constant(value=1), Constant(value=2)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(1, g=42)': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[Constant(value=1)], keywords=[keyword(arg='g', value=Constant(value=42))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f5
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(1, 3, g=23)': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[Constant(value=1), Constant(value=3)], keywords=[keyword(arg='g', value=Constant(value=23))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f6
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(*seq)': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[Starred(value=Name(id='seq', ctx=Load()), ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f7
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'g(**{x: 2})': Unsupported AST node: Call(func=Name(id='g', ctx=Load()), args=[], keywords=[keyword(value=Dict(keys=[Name(id='x', ctx=Load())], values=[Constant(value=2)]))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not x.g': Unsupported AST node: Attribute(value=Name(id='x', ctx=Load()), attr='g', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.a': Unsupported AST node: Attribute(value=Name(id='x', ctx=Load()), attr='a', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b < a': Unknown symbol: b
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a > b > c': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a < b > c': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f4
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a < b <= c': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f5
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a < b': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 11': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f1
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f2
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'myany(A() < 0)': Unsupported AST node: Call(func=Name(id='myany', ctx=Load()), args=[Compare(left=Call(func=Name(id='A', ctx=Load()), args=[], keywords=[]), ops=[Lt()], comparators=[Constant(value=0)])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '0 == f.a': Unsupported AST node: Attribute(value=Name(id='f', ctx=Load()), attr='a', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: f
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not a.name': Unsupported AST node: Attribute(value=Name(id='a', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/test_assertrewrite.py
FUNCTION: loc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'frame': Unknown symbol: frame
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_pprint.py
FUNCTION: test_consistent_pretty_printer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'PrettyPrinter().pformat(data) == textwrap.dedent(expected).strip()': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='PrettyPrinter', ctx=Load()), args=[], keywords=[]), attr='pformat', ctx=Load()), args=[Name(id='data', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_terminal_width_COLUMNS
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'terminalwriter.get_terminal_width() == 42': Unsupported AST node: Call(func=Attribute(value=Name(id='terminalwriter', ctx=Load()), attr='get_terminal_width', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_terminalwriter_width_bogus
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.fullwidth == 80': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='fullwidth', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_terminalwriter_computes_width
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.fullwidth == 42': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='fullwidth', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_terminalwriter_not_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'buffer.getvalue() == b'hello \\U0001f300 w\\xf4rld \\u05d0\\u05d1\\u05d2'': Unsupported AST node: Call(func=Attribute(value=Name(id='buffer', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_attr_hasmarkup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not tw.hasmarkup': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='hasmarkup', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: assert_color
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.hasmarkup is expected': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='hasmarkup', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_code_highlight
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f.getvalue().splitlines(keepends=True) == color_mapping.format([expected])': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='f', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[]), attr='splitlines', ctx=Load()), args=[], keywords=[keyword(arg='keepends', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_highlight_empty_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f.getvalue() == ''': Unsupported AST node: Call(func=Attribute(value=Name(id='f', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_line
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_line_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines[0] == msg + '\n'': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_sep_no_title
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_sep_with_title
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_sep_longer_than_width
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'line == '- aaaaaaaaaa -\n'': Unknown symbol: line
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_markup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''hello' in text': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_attr_fullwidth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines[0]) == len(lines[1])': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_init
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.width_of_current_line == 0': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='width_of_current_line', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_update
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.width_of_current_line == 11': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='width_of_current_line', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_update_with_newline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.width_of_current_line == 5': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='width_of_current_line', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_update_with_wide_text
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw.width_of_current_line == 21': Unsupported AST node: Attribute(value=Name(id='tw', ctx=Load()), attr='width_of_current_line', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_composed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(text) == 9': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='text', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_terminalwriter.py
FUNCTION: test_combining
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(text) == 10': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='text', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_wcwidth.py
FUNCTION: test_wcwidth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'wcwidth(c) == expected': Unsupported AST node: Call(func=Name(id='wcwidth', ctx=Load()), args=[Name(id='c', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_wcwidth.py
FUNCTION: test_wcswidth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'wcswidth(s) == expected': Unsupported AST node: Call(func=Name(id='wcswidth', ctx=Load()), args=[Name(id='s', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_simple_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr(1) == '1'': Unsupported AST node: Call(func=Name(id='saferepr', ctx=Load()), args=[Constant(value=1)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_maxsize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(s) == 25': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='s', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_no_maxsize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == expected': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_maxsize_error_on_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(s) == 25': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='s', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_exceptions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Exception' in saferepr(BrokenRepr(Exception('broken')))': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_baseexception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr(obj) == f'<[unpresentable exception ({baseexc_str!r}) raised in repr()] BrokenObj object at 0x{id(obj):x}>'': Unsupported AST node: Call(func=Name(id='saferepr', ctx=Load()), args=[Name(id='obj', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_buggy_builtin_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''Buggy' in saferepr(int())': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_big_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(saferepr(range(1000))) <= len('[' + SafeRepr(0).maxlist * '1000' + ']')': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Call(func=Name(id='saferepr', ctx=Load()), args=[Call(func=Name(id='range', ctx=Load()), args=[Constant(value=1000)], keywords=[])], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_repr_on_newstyle
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr(Function())': Unsupported AST node: Call(func=Name(id='saferepr', ctx=Load()), args=[Call(func=Name(id='Function', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr(val) == reprval': Unsupported AST node: Call(func=Name(id='saferepr', ctx=Load()), args=[Name(id='val', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_broken_getattribute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr(SomeClass()).startswith('<[RuntimeError() raised in repr()] SomeClass object at 0x')': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='saferepr', ctx=Load()), args=[Call(func=Name(id='SomeClass', ctx=Load()), args=[], keywords=[])], keywords=[]), attr='startswith', ctx=Load()), args=[Constant(value='<[RuntimeError() raised in repr()] SomeClass object at 0x')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_saferepr_unlimited
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr_unlimited(dict5) == "{'v0': 0, 'v1': 1, 'v2': 2, 'v3': 3, 'v4': 4}"': Unsupported AST node: Call(func=Name(id='saferepr_unlimited', ctx=Load()), args=[Name(id='dict5', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/io/test_saferepr.py
FUNCTION: test_saferepr_unlimited_exc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'saferepr_unlimited(A()).startswith('<[ValueError(42) raised in repr()] A object at 0x')': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='saferepr_unlimited', ctx=Load()), args=[Call(func=Name(id='A', ctx=Load()), args=[], keywords=[])], keywords=[]), attr='startswith', ctx=Load()), args=[Constant(value='<[ValueError(42) raised in repr()] A object at 0x')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/issue_519.py
FUNCTION: checked_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'order == [('issue_519.py', 'fix1', 'arg1v1'), ('test_one[arg1v1-arg2v1]', 'fix2', 'arg2v1'), ('test_two[arg1v1-arg2v1]', 'fix2', 'arg2v1'), ('test_one[arg1v1-arg2v2]', 'fix2', 'arg2v2'), ('test_two[arg1v1-arg2v2]', 'fix2', 'arg2v2'), ('issue_519.py', 'fix1', 'arg1v2'), ('test_one[arg1v2-arg2v1]', 'fix2', 'arg2v1'), ('test_two[arg1v2-arg2v1]', 'fix2', 'arg2v1'), ('test_one[arg1v2-arg2v2]', 'fix2', 'arg2v2'), ('test_two[arg1v2-arg2v2]', 'fix2', 'arg2v2')]': Unknown symbol: order
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/test_getfixturevalue_dynamic.py
FUNCTION: test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'request.fixturenames == ['b', 'request', 'a', 'dynamic']': Unsupported AST node: Attribute(value=Name(id='request', ctx=Load()), attr='fixturenames', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_extend_fixture_module_class.py
FUNCTION: test_spam
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'spam == 'spamspam'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_funcarg_lookup_modulelevel.py
FUNCTION: test_func
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'something == 'test_func'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_funcarg_lookup_modulelevel.py
FUNCTION: test_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'something == 'test_method'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_funcarg_lookup_classlevel.py
FUNCTION: test_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'something is self': Unsupported compare op: <class 'ast.Is'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_extend_fixture_conftest_conftest/pkg/test_spam.py
FUNCTION: test_spam
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'spam == 'spamspam'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/fixtures/fill_fixtures/test_extend_fixture_conftest_module/test_extend_fixture_conftest_module.py
FUNCTION: test_spam
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'spam == 'spamspam'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_recursive_dataclasses.py
FUNCTION: test_recursive_dataclasses
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_dataclasses_verbose.py
FUNCTION: test_dataclasses_verbose
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_two_different_dataclasses.py
FUNCTION: test_comparing_two_different_data_classes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left != right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_initvar.py
FUNCTION: test_demonstrate
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'Foo(1, 2) == Foo(1, 3)': Unsupported AST node: Call(func=Name(id='Foo', ctx=Load()), args=[Constant(value=1), Constant(value=2)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_dataclasses_with_custom_eq.py
FUNCTION: test_dataclasses
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_dataclasses.py
FUNCTION: test_dataclasses
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/dataclasses/test_compare_dataclasses_field_comparison_off.py
FUNCTION: test_dataclasses_with_attribute_comparison_off
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'left == right': Unknown symbol: left
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip_class.py
FUNCTION: setUpClass
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip_class.py
FUNCTION: test_foo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip_module.py
FUNCTION: setUpModule
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip_module.py
FUNCTION: test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_unittest_asynctest.py
FUNCTION: test_teardowns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(teardowns) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='teardowns', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip.py
FUNCTION: setUp
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_setup_skip.py
FUNCTION: test_foo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Audit error: b'Sort mismatch at argument #1 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/unittest/test_unittest_asyncio.py
FUNCTION: test_teardowns
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(teardowns) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='teardowns', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/doctest/main_py/test_normal_module.py
FUNCTION: test_doc
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/tmpdir/tmp_path_fixture.py
FUNCTION: test_fixture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tmp_path.is_dir()': Unsupported AST node: Call(func=Attribute(value=Name(id='tmp_path', ctx=Load()), attr='is_dir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/example_scripts/acceptance/fixture_mock_integration.py
FUNCTION: test_foobar
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'my_fixture == 'MOCKED'': b'parser error'
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_formatter.py
FUNCTION: test_coloredlogformatter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output == 'dummypath                   10 \x1b[32mINFO    \x1b[0m Test Message'': Unknown symbol: output
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_formatter.py
FUNCTION: test_coloredlogformatter_with_width_precision
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output == 'dummypath                   10 \x1b[32mINFO    \x1b[0m Test Message'': Unknown symbol: output
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_formatter.py
FUNCTION: test_multiline_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output == 'dummypath                   10 INFO     Test Message line1\n                                        line2'': Unknown symbol: output
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_formatter.py
FUNCTION: test_colored_short_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output == '\x1b[32mI\x1b[0m Test Message'': Unknown symbol: output
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_nothing_logged
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_messages_logged
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_root_logger_affected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_cli_level_log_level_interaction
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_setup_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_teardown_logging
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_cli_default_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_sections_single_new_line_after_test_outcome
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 're.search('(.+)live log teardown(.+)\\nWARNING(.+)\\nWARNING(.+)', result.stdout.str(), re.MULTILINE) is not None': Unsupported AST node: Call(func=Attribute(value=Name(id='re', ctx=Load()), attr='search', ctx=Load()), args=[Constant(value='(.+)live log teardown(.+)\\nWARNING(.+)\\nWARNING(.+)'), Call(func=Attribute(value=Attribute(value=Name(id='result', ctx=Load()), attr='stdout', ctx=Load()), attr='str', ctx=Load()), args=[], keywords=[]), Attribute(value=Name(id='re', ctx=Load()), attr='MULTILINE', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_cli_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_cli_ini_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_cli
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_mode_cli
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_mode_cli_invalid
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.USAGE_ERROR': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_cli_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_mode_ini
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_ini_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_live_logging_suspends_capture
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'cast(io.StringIO, out_file).getvalue() == '\nsome message\n'': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='cast', ctx=Load()), args=[Attribute(value=Name(id='io', ctx=Load()), attr='StringIO', ctx=Load()), Name(id='out_file', ctx=Load())], keywords=[]), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_collection_logging_to_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_set_path_with_log_file_mode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_colored_captured_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_colored_ansi_esc_caplogtext
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_cli_subdirectories_are_successfully_created
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''logf.log' in os.listdir(expected)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_disable_loggers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_disable_loggers_does_not_propagate
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_disabling_works_with_log_cli
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_without_date_format_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_date_format_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_date_format_percentf_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_date_format_percentf_tz_log
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_reporting.py
FUNCTION: test_log_file_cli_fallback_options
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_change_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''DEBUG' not in caplog.text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_change_level_logging_disabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'logging.root.manager.disable == logging.CRITICAL': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Name(id='logging', ctx=Load()), attr='root', ctx=Load()), attr='manager', ctx=Load()), attr='disable', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_with_statement_at_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''DEBUG' not in caplog.text': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_with_statement_at_level_logging_disabled
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'logging.root.manager.disable == logging.CRITICAL': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Name(id='logging', ctx=Load()), attr='root', ctx=Load()), attr='manager', ctx=Load()), attr='disable', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_with_statement_filtering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'filtered_tuple == ('test_fixture', 20, 'filtered handler call')': Unknown symbol: filtered_tuple
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_force_enable_logging_level_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not test_logger.isEnabledFor(logging.CRITICAL)': Unsupported AST node: Call(func=Attribute(value=Name(id='test_logger', ctx=Load()), attr='isEnabledFor', ctx=Load()), args=[Attribute(value=Name(id='logging', ctx=Load()), attr='CRITICAL', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_log_access
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'caplog.records[0].levelname == 'INFO'': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='caplog', ctx=Load()), attr='records', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='levelname', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_messages
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''boo arg' == caplog.messages[0]': Unsupported AST node: Subscript(value=Attribute(value=Name(id='caplog', ctx=Load()), attr='messages', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_record_tuples
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'caplog.record_tuples == [(__name__, logging.INFO, 'boo arg')]': Unsupported AST node: Attribute(value=Name(id='caplog', ctx=Load()), attr='record_tuples', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'caplog.records[0].levelname == 'INFO'': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='caplog', ctx=Load()), attr='records', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='levelname', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_clear
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(caplog.records)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='caplog', ctx=Load()), attr='records', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: logging_during_setup_and_teardown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[x.message for x in caplog.get_records('teardown')] == ['a_teardown_log']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='message', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Call(func=Attribute(value=Name(id='caplog', ctx=Load()), attr='get_records', ctx=Load()), args=[Constant(value='teardown')], keywords=[]), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: private_assert_caplog_records_is_setup_call
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'set(caplog_records) == {'setup', 'call'}': Unsupported AST node: Call(func=Name(id='set', ctx=Load()), args=[Name(id='caplog_records', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_captures_for_all_stages
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not caplog.records': Unsupported AST node: Attribute(value=Name(id='caplog', ctx=Load()), attr='records', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_clear_for_call_stage
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[x.message for x in caplog.get_records('call')] == ['a_call_log']': Unsupported AST node: ListComp(elt=Attribute(value=Name(id='x', ctx=Load()), attr='message', ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Call(func=Attribute(value=Name(id='caplog', ctx=Load()), attr='get_records', ctx=Load()), args=[Constant(value='call')], keywords=[]), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_ini_controls_global_log_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_can_override_global_log_level
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_captures_despite_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/logging/test_fixture.py
FUNCTION: test_log_report_captures_according_to_config_option_upon_failure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/freeze/tests/test_trivial.py
FUNCTION: test_upper
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''foo'.upper() == 'FOO'': Unsupported AST node: Call(func=Attribute(value=Constant(value='foo'), attr='upper', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/freeze/tests/test_trivial.py
FUNCTION: test_lower
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''FOO'.lower() == 'foo'': Unsupported AST node: Call(func=Attribute(value=Constant(value='FOO'), attr='lower', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/plugins_integration/bdd_wallet.py
FUNCTION: check
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'wallet.amount == 47': Unsupported AST node: Attribute(value=Name(id='wallet', ctx=Load()), attr='amount', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_no_funcargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not metafunc.fixturenames': Unsupported AST node: Attribute(value=Name(id='metafunc', ctx=Load()), attr='fixturenames', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_function_basic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(metafunc.fixturenames) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='metafunc', ctx=Load()), attr='fixturenames', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_error_iterator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[(x.params, x.id) for x in metafunc._calls] == [({'x': 1}, '0'), ({'x': 2}, '2')]': Unsupported AST node: ListComp(elt=Tuple(elts=[Attribute(value=Name(id='x', ctx=Load()), attr='params', ctx=Load()), Attribute(value=Name(id='x', ctx=Load()), attr='id', ctx=Load())], ctx=Load()), generators=[comprehension(target=Name(id='x', ctx=Store()), iter=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), ifs=[], is_async=0)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_find_parametrized_scope
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'find_scope(['func_fix'], indirect=True) == Scope.Function': Unsupported AST node: Call(func=Name(id='find_scope', ctx=Load()), args=[List(elts=[Constant(value='func_fix')], ctx=Load())], keywords=[keyword(arg='indirect', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_and_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ids == ['basic-abc', 'basic-def', 'advanced-abc', 'advanced-def']': Unknown symbol: ids
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_and_id_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ids == ['basic', 'advanced']': Unknown symbol: ids
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_ids_iterator_without_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ids == ['0-2', '0-3', '1-2', '1-3']': Unknown symbol: ids
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_empty_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''skip' == metafunc._calls[0].marks[0].name': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='marks', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_with_userobjects
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'metafunc._calls[0].id == 'x0-a'': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='id', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idval_hypothesis
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(escaped, str)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='escaped', ctx=Load()), Name(id='str', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_notset_idval
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'IdMaker([], [], None, None, None, None, None)._idval(NOTSET, 'a', 0) == 'a0'': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='IdMaker', ctx=Load()), args=[List(elts=[], ctx=Load()), List(elts=[], ctx=Load()), Constant(value=None), Constant(value=None), Constant(value=None), Constant(value=None), Constant(value=None)], keywords=[]), attr='_idval', ctx=Load()), args=[Name(id='NOTSET', ctx=Load()), Constant(value='a'), Constant(value=0)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_autoname
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['string-1.0', 'st-ring-2.0']': Unsupported AST node: List(elts=[Constant(value='string-1.0'), Constant(value='st-ring-2.0')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_with_bytes_regex
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['foo']': Unsupported AST node: List(elts=[Constant(value='foo')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_native_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['1.0--1.1', '2--202', 'three-three hundred', 'True-False', 'None-None', 'foo-bar', 'str-int', 'a7-b7', 'a8-b8', 'a9-b9', '\\xc3\\xb4-name', '\\xc3\\xb4-other', '1j-(-0-2j)']': Unsupported AST node: List(elts=[Constant(value='1.0--1.1'), Constant(value='2--202'), Constant(value='three-three hundred'), Constant(value='True-False'), Constant(value='None-None'), Constant(value='foo-bar'), Constant(value='str-int'), Constant(value='a7-b7'), Constant(value='a8-b8'), Constant(value='a9-b9'), Constant(value='\\xc3\\xb4-name'), Constant(value='\\xc3\\xb4-other'), Constant(value='1j-(-0-2j)')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_non_printable_characters
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['\\x00-1', '\\x05-2', '\\x00-3', '\\x05-4', '\\t-5', '\\t-6']': Unsupported AST node: List(elts=[Constant(value='\\x00-1'), Constant(value='\\x05-2'), Constant(value='\\x00-3'), Constant(value='\\x05-4'), Constant(value='\\t-5'), Constant(value='\\t-6')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_manual_ids_must_be_printable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['hello \\x00', 'hello \\x05']': Unsupported AST node: List(elts=[Constant(value='hello \\x00'), Constant(value='hello \\x05')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_enum
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['Foo.one-Foo.two']': Unsupported AST node: List(elts=[Constant(value='Foo.one-Foo.two')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_idfn
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['10.0-IndexError()', '20-KeyError()', 'three-b2']': Unsupported AST node: List(elts=[Constant(value='10.0-IndexError()'), Constant(value='20-KeyError()'), Constant(value='three-b2')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_idfn_unique_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['a-a0', 'a-a1', 'a-a2']': Unsupported AST node: List(elts=[Constant(value='a-a0'), Constant(value='a-a1'), Constant(value='a-a2')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_duplicated_empty_str
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['0', '1']': Unsupported AST node: List(elts=[Constant(value='0'), Constant(value='1')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_with_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['a', '3-4']': Unsupported AST node: List(elts=[Constant(value='a'), Constant(value='3-4')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_with_paramset_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['me', 'you']': Unsupported AST node: List(elts=[Constant(value='me'), Constant(value='you')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_idmaker_with_ids_unique_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result == ['a0', 'a1', 'b0', 'c', 'b1']': Unsupported AST node: List(elts=[Constant(value='a0'), Constant(value='a1'), Constant(value='b0'), Constant(value='c'), Constant(value='b1')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_indirect
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(metafunc._calls) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_indirect_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'metafunc._calls[0].params == dict(x='a', y='b')': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='params', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_indirect_list_all
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'metafunc._calls[0].params == dict(x='a', y='b')': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='params', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_indirect_list_empty
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'metafunc._calls[0].params == dict(x='a', y='b')': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='params', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_onearg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(metafunc._calls) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_onearg_indirect
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'metafunc._calls[0].params == dict(x=1)': Unsupported AST node: Attribute(value=Subscript(value=Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='params', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_twoargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(metafunc._calls) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='metafunc', ctx=Load()), attr='_calls', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_multiple_times
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_class_scenarios
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_with_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_with_None_in_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_with_identical_ids_get_unique_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_issue323
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not reprec.getcalls('pytest_internalerror')': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='getcalls', ctx=Load()), args=[Constant(value='pytest_internalerror')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_missing_scope_doesnt_crash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_module_level_test_with_class_scope
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(test_1_0, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='test_1_0', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_reordering_with_scopeless_and_just_indirect_parametrization
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_some_arguments_auto_scope
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'func_fix_setup == [True] * 4': Unknown symbol: func_fix_setup
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_issue634
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'output.count('preparing foo-2') == 1': Unsupported AST node: Call(func=Attribute(value=Name(id='output', ctx=Load()), attr='count', ctx=Load()), args=[Constant(value='preparing foo-2')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_simple_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_select_based_on_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(passed) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='passed', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_parametrize_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'names == ['test_func[paramset1]', 'test_func', 'test_func[paramset3]']': Unknown symbol: names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_param_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'names == ['test_func[paramset1]', 'test_func', 'test_func[c-z]']': Unknown symbol: names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/metafunc.py
FUNCTION: test_multiple_parametrize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'names == ['test_func[a-x]', 'test_func[a-y]', 'test_func[x]', 'test_func[y]']': Unknown symbol: names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: do_assert
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(obtained_message) == len(expected_message)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='obtained_message', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_error_messages_invalid_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'message == '\n'.join(['  ', '  Impossible to compare arrays with different shapes.', '  Shapes: (2, 1) and (2, 2)'])': Unknown symbol: message
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_repr_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(approx(1.0)) == '1.0 ± 1.0e-06'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Call(func=Name(id='approx', ctx=Load()), args=[Constant(value=1.0)], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_repr_complex_numbers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(approx(inf + 1j)) == '(inf+1j)'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Call(func=Name(id='approx', ctx=Load()), args=[BinOp(left=Name(id='inf', ctx=Load()), op=Add(), right=Constant(value=1j))], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_repr_nd_array
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(approx(np_array)) == expected_repr_string': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Call(func=Name(id='approx', ctx=Load()), args=[Name(id='np_array', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_bool
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'err.match('approx\\(\\) is not supported in a boolean context')': Unsupported AST node: Call(func=Attribute(value=Name(id='err', ctx=Load()), attr='match', ctx=Load()), args=[Constant(value='approx\\(\\) is not supported in a boolean context')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_mixed_sequence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[1.1, 2, 'word'] == pytest.approx([1.1, 2, 'word'])': Unsupported AST node: List(elts=[Constant(value=1.1), Constant(value=2), Constant(value='word')], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_operator_overloading
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '1 == approx(1, rel=1e-06, abs=1e-12)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Constant(value=1)], keywords=[keyword(arg='rel', value=Constant(value=1e-06)), keyword(arg='abs', value=Constant(value=1e-12))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_reasonable_defaults
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '0.1 + 0.2 == approx(0.3)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Constant(value=0.3)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_custom_tolerances
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '100000000.0 + 1.0 == approx(100000000.0, rel=5e-08, abs=5.0)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Constant(value=100000000.0)], keywords=[keyword(arg='rel', value=Constant(value=5e-08)), keyword(arg='abs', value=Constant(value=5.0))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_expecting_bool
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'True == approx(True)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Constant(value=True)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_expecting_bool_numpy
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'np.False_ != approx(True)': Unsupported AST node: Attribute(value=Name(id='np', ctx=Load()), attr='False_', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_list_decimal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_list_wrong_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[1, 2] != approx([1])': Unsupported AST node: List(elts=[Constant(value=1), Constant(value=2)], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_tuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_tuple_wrong_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(1, 2) != approx((1,))': Unsupported AST node: Tuple(elts=[Constant(value=1), Constant(value=2)], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_tuple_vs_other
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '1 != approx((1,))': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Tuple(elts=[Constant(value=1)], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_dict
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_dict_decimal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_dict_wrong_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{'a': 1, 'b': 2} != approx({'a': 1})': Unsupported AST node: Dict(keys=[Constant(value='a'), Constant(value='b')], values=[Constant(value=1), Constant(value=2)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_dict_nonnumeric
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '{'a': 1.0, 'b': None} == pytest.approx({'a': 1.0, 'b': None})': Unsupported AST node: Dict(keys=[Constant(value='a'), Constant(value='b')], values=[Constant(value=1.0), Constant(value=None)])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_dict_vs_other
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '1 != approx({'a': 0})': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Dict(keys=[Constant(value='a')], values=[Constant(value=0)])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_array
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_array_wrong_shape
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a12 != approx(a21)': Unknown symbol: a12
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_array_implicit_conversion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'vec1 != approx(vec2)': Unknown symbol: vec1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_array_protocol
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'approx(expected) == DeviceArray(actual, size=1)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Name(id='expected', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_doctests
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'approx.__doc__ is not None': Unsupported AST node: Attribute(value=Name(id='approx', ctx=Load()), attr='__doc__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_nonnumeric_okay_if_equal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == approx(x)': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Name(id='x', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_nonnumeric_false_if_unequal
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''ab' != approx('abc')': Unsupported AST node: Call(func=Name(id='approx', ctx=Load()), args=[Constant(value='abc')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_nonnumeric_dict_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(approx(x1)) == "approx({'foo': 1.0000005 ± 1.0e-06, 'bar': None, 'foobar': inf})"': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Call(func=Name(id='approx', ctx=Load()), args=[Name(id='x1', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_nonnumeric_list_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(approx(x1)) == 'approx([1.0000005 ± 1.0e-06, None, inf])'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Call(func=Name(id='approx', ctx=Load()), args=[Name(id='x1', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_array_with_scalar
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_numpy_scalar_with_array
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'actual == approx(expected, rel=5e-07, abs=0)': Unknown symbol: actual
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_generic_ordered_sequence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '[1, 2, 3, 4] == approx(expected, abs=0.0001)': Unsupported AST node: List(elts=[Constant(value=1), Constant(value=2), Constant(value=3), Constant(value=4)], ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_decimal_approx_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'decimal.Decimal('2.600001') == approx_obj': Unsupported AST node: Call(func=Attribute(value=Name(id='decimal', ctx=Load()), attr='Decimal', ctx=Load()), args=[Constant(value='2.600001')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_strange_sequence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b == pytest.approx(a, abs=2)': Unknown symbol: b
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_scalar
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, 16) == 4': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), Constant(value=16)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_empty_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, []) == []': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), List(elts=[], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_list
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, [4, 16, 25, 676]) == [2, 4, 5, 26]': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), List(elts=[Constant(value=4), Constant(value=16), Constant(value=25), Constant(value=676)], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_tuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, (4, 16, 25, 676)) == (2, 4, 5, 26)': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), Tuple(elts=[Constant(value=4), Constant(value=16), Constant(value=25), Constant(value=676)], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_nested_lists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, [4, [25, 64], [[49]]]) == [2, [5, 8], [[7]]]': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), List(elts=[Constant(value=4), List(elts=[Constant(value=25), Constant(value=64)], ctx=Load()), List(elts=[List(elts=[Constant(value=49)], ctx=Load())], ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_mixed_sequence
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(sqrt, [4, (25, 64), [49]]) == [2, (5, 8), [7]]': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='sqrt', ctx=Load()), List(elts=[Constant(value=4), Tuple(elts=[Constant(value=25), Constant(value=64)], ctx=Load()), List(elts=[Constant(value=49)], ctx=Load())], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/approx.py
FUNCTION: test_map_over_sequence_like
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '_recursive_sequence_map(int, MyVec3(1, 2, 3)) == [1, 2, 3]': Unsupported AST node: Call(func=Name(id='_recursive_sequence_map', ctx=Load()), args=[Name(id='int', ctx=Load()), Call(func=Name(id='MyVec3', ctx=Load()), args=[Constant(value=1), Constant(value=2), Constant(value=3)], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_modulecol_roundtrip
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'modcol.name == newcol.name': Unsupported AST node: Attribute(value=Name(id='modcol', ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_customized_python_discovery
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_customized_python_discovery_functions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_unorderable_types
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_class_injection_does_not_break_collection
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''RuntimeError: dictionary changed size during iteration' not in result.stdout.str()': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_package_collection_init_given_as_argument
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_show_traceback_import_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_show_traceback_import_error_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 2': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_issue1035_obj_has_getattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(colitems) == 0': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='colitems', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_issue2234_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_does_not_discover_properties
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_does_not_discover_instance_descriptors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.NO_TESTS_COLLECTED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_abstract_class_is_not_collected
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_getmodulecollector
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(modcol, pytest.Module)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='modcol', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Module', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_function_equality
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'f1 == f1': Unknown symbol: f1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_repr_produces_actual_test_id
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(f) == '<Function test[\\xe5]>'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Name(id='f', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_parametrize_with_mark
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''foo' in keywords[0] and 'bar' not in keywords[0] and ('baz' not in keywords[0])': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_parametrize_with_empty_string_arguments
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'names == {'test[-]', 'test[ -]', 'test[- ]', 'test[ - ]'}': Unknown symbol: names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_function_equality_with_callspec
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'items[0] != items[1]': Unsupported AST node: Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_multiple_parametrize
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'colitems[0].name == 'test1[2-0]'': Unsupported AST node: Attribute(value=Subscript(value=Name(id='colitems', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_issue751_multiple_parametrize_with_ids
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'colitems[0].name == 'test1[a-c]'': Unsupported AST node: Attribute(value=Subscript(value=Name(id='colitems', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='name', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_function_originalname
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'originalnames == ['test_func', 'test_func', 'test_no_param']': Unknown symbol: originalnames
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_check_equality
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(fn1, pytest.Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='fn1', ctx=Load()), Attribute(value=Name(id='pytest', ctx=Load()), attr='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_allow_sane_sorting_for_decorators
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(colitems) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='colitems', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_early_ignored_attributes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'rec.ret == 0': Unsupported AST node: Attribute(value=Name(id='rec', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_skip_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.traceback[-1].ishidden(excinfo)': Unsupported AST node: Call(func=Attribute(value=Subscript(value=Attribute(value=Name(id='excinfo', ctx=Load()), attr='traceback', ctx=Load()), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load()), attr='ishidden', ctx=Load()), args=[Name(id='excinfo', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_traceback_argsetup
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_traceback_error_during_import
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_traceback_filter_error_during_fixture_collection
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_filter_traceback_generated_code
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tb is not None': Unknown symbol: tb
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_filter_traceback_path_no_longer_valid
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tb is not None': Unknown symbol: tb
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_itemreport_reportinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'item.location == ('ABCDE', 42, 'custom')': Unsupported AST node: Attribute(value=Name(id='item', ctx=Load()), attr='location', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_func_reportinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.fspath(path) == str(item.path)': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='fspath', ctx=Load()), args=[Name(id='path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_class_reportinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(classcol, Class)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='classcol', ctx=Load()), Name(id='Class', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/collect.py
FUNCTION: test_reportinfo_with_nasty_getattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(classcol, Class)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='classcol', ctx=Load()), Name(id='Class', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_functions
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not getfuncargnames(f)': Unsupported AST node: Call(func=Name(id='getfuncargnames', ctx=Load()), args=[Name(id='f', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_methods
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getfuncargnames(A().f) == ('arg1',)': Unsupported AST node: Call(func=Name(id='getfuncargnames', ctx=Load()), args=[Attribute(value=Call(func=Name(id='A', ctx=Load()), args=[], keywords=[]), attr='f', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_staticmethod
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getfuncargnames(A.static, cls=A) == ('arg1', 'arg2')': Unsupported AST node: Call(func=Name(id='getfuncargnames', ctx=Load()), args=[Attribute(value=Name(id='A', ctx=Load()), attr='static', ctx=Load())], keywords=[keyword(arg='cls', value=Name(id='A', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_staticmethod_inherited
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getfuncargnames(B.static, cls=B) == ('arg1', 'arg2')': Unsupported AST node: Call(func=Name(id='getfuncargnames', ctx=Load()), args=[Attribute(value=Name(id='B', ctx=Load()), attr='static', ctx=Load())], keywords=[keyword(arg='cls', value=Name(id='B', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_partial
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ('arg1', 'arg2')': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfuncargnames_staticmethod_partial
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ('arg1', 'arg2')': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_pytest_fixture_setup_and_post_finalizer_hook
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_fixture_arg_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_yield_fixture_with_no_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_deduplicate_names
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'items == ('a', 'b', 'c', 'd')': Unknown symbol: items
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_staticmethod_classmethod_fixture_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_scoped_fixture_caching
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_scoped_fixture_caching_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_scoped_fixture_teardown_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_subfixture_teardown_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_funcarg_lookupfails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_funcarg_basic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_extend_fixture_conftest_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_extend_fixture_plugin_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_autouse_fixture_plugin
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_fixture_excinfo_leak
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_attributes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_attributes_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_contains_funcarg_arg2fixturedefs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item1, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item1', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_getfixturevalue
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_addfinalizer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_addfinalizer_failing_setup_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not mod.values': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='values', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_getmodulepath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_fixtures_sub_subdir_normalize_sep
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_show_fixtures_color_yes
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''\x1b[32mtmp_path' in result.stdout.str()': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_applymarker
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(item1, Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='item1', ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_factory_setup_as_classes_fails
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_fixture_parametrized_with_iterator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == [1, 2, 10, 20]': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_class_function_parametrization_finalization
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ['fin_a1', 'fin_a2', 'fin_b1', 'fin_b2'] * 2': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_scope_mismatch_various
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_scope_mismatch_already_computed_dynamic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrize_and_scope
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrize_separated_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == [1, 1, 2, 2]': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrize_separated_order_higher_scope_first
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == expected': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrized_fixture_teardown_order
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_request_is_clean
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == [1, 2]': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrize_separated_lifecycle
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values[0] == values[1] == 1': Unsupported AST node: Subscript(value=Name(id='values', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_class_scope_parametrization_ordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ['test_hello', 'fin John', 'test_hello', 'fin Doe', 'test_name', 'test_population', 'fin John', 'test_name', 'test_population', 'fin Doe']': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_deterministic_fixture_collection
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(output1) == 12': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='output1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_subfactory_missing_funcarg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_setupfunc_missing_funcarg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_cached_exception_doesnt_get_longer
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.TESTS_FAILED': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_funcarg_compat
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'config.option.showfixtures': Unsupported AST node: Attribute(value=Attribute(value=Name(id='config', ctx=Load()), attr='option', ctx=Load()), attr='showfixtures', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_show_help
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not result.ret': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_module_auto
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_with_native_fixtures
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_scopes_reordered
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_same_scope_closer_root_first
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_func_closure_all_scopes_complex
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(items[0], Function)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Subscript(value=Name(id='items', ctx=Load()), slice=Constant(value=0), ctx=Load()), Name(id='Function', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/fixtures.py
FUNCTION: test_parametrized_package_scope_reordering
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == ExitCode.OK': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_no_items_should_not_show_output
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_fixtures_in_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_fixtures_in_conftest
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_should_show_fixtures_used_by_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_verbose_include_private_fixtures_and_loc
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_doctest_items
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_multiline_docstring_in_module
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/show_fixtures_per_test.py
FUNCTION: test_verbose_include_multiline_docstring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: fails_raises_group
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg[-1] != '\n'': Unsupported AST node: Subscript(value=Name(id='msg', ctx=Load()), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: test_matches
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not rg.matches(None)': Unsupported AST node: Call(func=Attribute(value=Name(id='rg', ctx=Load()), attr='matches', ctx=Load()), args=[Constant(value=None)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: test_raisesexc_tostring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(RaisesExc(ValueError)) == 'RaisesExc(ValueError)'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Name(id='RaisesExc', ctx=Load()), args=[Name(id='ValueError', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: test_raisesgroup_tostring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(RaisesGroup(ValueError, match='[a-z]', check=bool)) == f"RaisesGroup(ValueError, match='[a-z]', check={bool!r})"': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Name(id='RaisesGroup', ctx=Load()), args=[Name(id='ValueError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='[a-z]')), keyword(arg='check', value=Name(id='bool', ctx=Load()))])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: test_assert_matches
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'RaisesExc(ValueError).matches(e)': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='RaisesExc', ctx=Load()), args=[Name(id='ValueError', ctx=Load())], keywords=[]), attr='matches', ctx=Load()), args=[Name(id='e', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises_group.py
FUNCTION: check_str_and_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == str(evaled) == repr(evaled)': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='evaled', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_wrapped_getfslineno
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lineno > lineno2': Unknown symbol: lineno
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_pytestconfig_is_session_scoped
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'marker is not None': Unknown symbol: marker
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_function_instance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(items) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='items', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_wrapped_getfuncargnames
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ('x',)': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_getfuncargnames_patching
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'values == ('y', 'z')': Unknown symbol: values
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_mock
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'funcnames == ['T.test_hello', 'test_something']': Unknown symbol: funcnames
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_mock_sorting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'names == ['test_one', 'test_two', 'test_three']': Unknown symbol: names
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_module_with_global_test
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not reprec.getfailedcollections()': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='getfailedcollections', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_class_and_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not reprec.getfailedcollections()': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='getfailedcollections', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_unittest_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not reprec.getfailedcollections()': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='getfailedcollections', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/integration.py
FUNCTION: test_class_with_nasty_getattr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not reprec.getfailedcollections()': Unsupported AST node: Call(func=Attribute(value=Name(id='reprec', ctx=Load()), attr='getfailedcollections', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_raises
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''invalid literal' in str(excinfo.value)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_raises_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''invalid literal' in str(excinfo.value)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_raises_cyclic_reference
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'sys.exc_info() == (None, None, None)': Unsupported AST node: Call(func=Attribute(value=Name(id='sys', ctx=Load()), attr='exc_info', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_raises_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(excinfo.value) == expr': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Attribute(value=Name(id='excinfo', ctx=Load()), attr='value', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_match_failure_string_quoting
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg == 'Regex pattern did not match.\n Regex: "\'foo"\n Input: "\'bar"'': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_match_failure_exact_string_message
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg == "Regex pattern did not match.\n Regex: 'Oh here is a message with (42) numbers in parameters'\n Input: 'Oh here is a message with (42) numbers in parameters'\n Did you mean to `re.escape()` the regex?"': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: test_raises_with_raising_dunder_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''via __class__' in excinfo.value.args[0]': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/python/raises.py
FUNCTION: __class__
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_ne
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'code1 == code1': Unknown symbol: code1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_code_gives_back_name_for_not_existing_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'co_code.co_filename == name': Unsupported AST node: Attribute(value=Name(id='co_code', ctx=Load()), attr='co_filename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_code_fullsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''test_code_fullsource()' in str(full)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_code_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(src) == expected': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='src', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_frame_getsourcelineno_myself
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_code_from_func
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'co.firstlineno': Unsupported AST node: Attribute(value=Name(id='co', ctx=Load()), attr='firstlineno', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_code_getargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'c1.getargs(var=True) == ('x',)': Unsupported AST node: Call(func=Attribute(value=Name(id='c1', ctx=Load()), attr='getargs', ctx=Load()), args=[], keywords=[keyword(arg='var', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_frame_getargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fr1.getargs(var=True) == [('x', 'a')]': Unsupported AST node: Call(func=Attribute(value=Name(id='fr1', ctx=Load()), attr='getargs', ctx=Load()), args=[], keywords=[keyword(arg='var', value=Constant(value=True))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_ExceptionChainRepr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr1 != repr2': Unknown symbol: repr1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_bad_getsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exci.getrepr()': Unsupported AST node: Call(func=Attribute(value=Name(id='exci', ctx=Load()), attr='getrepr', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_getsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_tb_entry_str
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 're.match(pattern, entry)': Unsupported AST node: Call(func=Attribute(value=Name(id='re', ctx=Load()), attr='match', ctx=Load()), args=[Name(id='pattern', ctx=Load()), Name(id='entry', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_code.py
FUNCTION: test_not_raise_exception_with_mixed_encoding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == "unicode_string = São Paulo, utf8_string = b'S\\xc3\\xa3o Paulo'"': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'info.type == ValueError': Unsupported AST node: Attribute(value=Name(id='info', ctx=Load()), attr='type', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_from_exc_info_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'info.type == ValueError': Unsupported AST node: Attribute(value=Name(id='info', ctx=Load()), attr='type', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_from_exception_simple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'info.type == ValueError': Unsupported AST node: Attribute(value=Name(id='info', ctx=Load()), attr='type', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_getstatement
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'foundlinenumbers == linenumbers': Unknown symbol: foundlinenumbers
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_exconly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.exconly().startswith('ValueError')': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='excinfo', ctx=Load()), attr='exconly', ctx=Load()), args=[], keywords=[]), attr='startswith', ctx=Load()), args=[Constant(value='ValueError')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_repr_str
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr(excinfo1) == '<ExceptionInfo ValueError() tblen=4>'': Unsupported AST node: Call(func=Name(id='repr', ctx=Load()), args=[Name(id='excinfo1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_for_later
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''for raises' in repr(e)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_excinfo_errisinstance
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.errisinstance(ValueError)': Unsupported AST node: Call(func=Attribute(value=Name(id='excinfo', ctx=Load()), attr='errisinstance', ctx=Load()), args=[Name(id='ValueError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_entrysource_Queue_example
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_codepath_Queue_example
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(path, Path)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='path', ctx=Load()), Name(id='Path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_match_raises_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret != 0': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_raises_accepts_generic_group
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_raises_accepts_generic_base_group
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_raises_accepts_generic_group_in_tuple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_traceback_with_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr_traceback is not None': Unknown symbol: repr_traceback
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_no_recursion_index_on_recursion_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''maximum recursion' in str(excinfo.getrepr())': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_exceptiongroup_short_summary_info
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_all_entries_hidden
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_hidden_entries_of_chained_exceptions_are_not_shown
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'result.ret == 1': Unsupported AST node: Attribute(value=Name(id='result', ctx=Load()), attr='ret', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_entries
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(tb) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='tb', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_entry_getsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's.startswith('def f():')': Unsupported AST node: Call(func=Attribute(value=Name(id='s', ctx=Load()), attr='startswith', ctx=Load()), args=[Constant(value='def f():')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_entry_getsource_in_construct
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_cut
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(path, Path)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='path', ctx=Load()), Name(id='Path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_cut_excludepath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newtraceback[-1].frame.code.path == p': Unsupported AST node: Attribute(value=Attribute(value=Attribute(value=Subscript(value=Name(id='newtraceback', ctx=Load()), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load()), attr='frame', ctx=Load()), attr='code', ctx=Load()), attr='path', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_filter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(ntraceback) == len(traceback) - 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='ntraceback', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_recursion_index
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'recindex == 3': Unknown symbol: recindex
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_only_specific_recursion_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''RuntimeError: hello' in str(repr.reprcrash)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_no_recursion_index
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo is not None': Unknown symbol: excinfo
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_messy_recursion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo.traceback.recursionindex() is None': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='excinfo', ctx=Load()), attr='traceback', ctx=Load()), attr='recursionindex', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_getreprcrash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprcrash is not None': Unknown symbol: reprcrash
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_getreprcrash_empty
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'excinfo._getreprcrash() is None': Unsupported AST node: Call(func=Attribute(value=Name(id='excinfo', ctx=Load()), attr='_getreprcrash', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_doesnt_contain_exception_type
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, match='^exception message$')': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_doesnt_contain_exception_match
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not exc_info.group_contains(RuntimeError, match='^exception message$')': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_type_unlimited_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_type_at_depth_1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, depth=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='depth', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_doesnt_contain_exception_type_past_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not exc_info.group_contains(RuntimeError, depth=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='depth', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_type_specific_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, depth=2)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='depth', value=Constant(value=2))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_match_unlimited_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, match='^exception message$')': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_match_at_depth_1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, match='^exception message$', depth=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$')), keyword(arg='depth', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_doesnt_contain_exception_match_past_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not exc_info.group_contains(RuntimeError, match='^exception message$', depth=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$')), keyword(arg='depth', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_contains_exception_match_specific_depth
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'exc_info.group_contains(RuntimeError, match='^exception message$', depth=2)': Unsupported AST node: Call(func=Attribute(value=Name(id='exc_info', ctx=Load()), attr='group_contains', ctx=Load()), args=[Name(id='RuntimeError', ctx=Load())], keywords=[keyword(arg='match', value=Constant(value='^exception message$')), keyword(arg='depth', value=Constant(value=2))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_source_out_of_bounds
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lines) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_source_excinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source is not None': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_source_not_existing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr.reprtraceback.reprentries[1].lines[0] == '>   ???'': Unsupported AST node: Subscript(value=Attribute(value=Subscript(value=Attribute(value=Attribute(value=Name(id='repr', ctx=Load()), attr='reprtraceback', ctx=Load()), attr='reprentries', ctx=Load()), slice=Constant(value=1), ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_many_line_source_not_existing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr.reprtraceback.reprentries[1].lines[0] == '>   ???'': Unsupported AST node: Subscript(value=Attribute(value=Subscript(value=Attribute(value=Attribute(value=Name(id='repr', ctx=Load()), attr='reprtraceback', ctx=Load()), attr='reprentries', ctx=Load()), slice=Constant(value=1), ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_source_failing_fullsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr.reprtraceback.reprentries[0].lines[0] == '>   ???'': Unsupported AST node: Subscript(value=Attribute(value=Subscript(value=Attribute(value=Attribute(value=Name(id='repr', ctx=Load()), attr='reprtraceback', ctx=Load()), attr='reprentries', ctx=Load()), slice=Constant(value=0), ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_local
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprlocals is not None': Unknown symbol: reprlocals
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_local_with_error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprlocals is not None': Unknown symbol: reprlocals
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_local_with_exception_in_class_property
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprlocals is not None': Unknown symbol: reprlocals
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_local_truncated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'truncated_reprlocals is not None': Unknown symbol: truncated_reprlocals
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_args_not_truncated
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprfuncargs is not None': Unknown symbol: reprfuncargs
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_tracebackentry_lines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines[0] == '    def func1():'': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_tracebackentry_lines2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprfuncargs is not None': Unknown symbol: reprfuncargs
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_tracebackentry_lines_var_kw_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'reprfuncargs is not None': Unknown symbol: reprfuncargs
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_tracebackentry_short
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines[0] == '    func1()'': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_traceback_entry_short_carets
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reprtb.lines) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='reprtb', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_tracebackentry_no
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines[0] == 'E   ValueError: hello'': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_traceback_tbfilter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(reprtb.reprentries) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='reprtb', ctx=Load()), attr='reprentries', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_short_no_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lines[0] == '    func1()'': Unsupported AST node: Subscript(value=Name(id='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_traceback_with_invalid_cwd
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p._makepath(Path(__file__)) == __file__': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='_makepath', ctx=Load()), args=[Call(func=Name(id='Path', ctx=Load()), args=[Name(id='__file__', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_excinfo_addouterr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[-1] == 'content'': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=UnaryOp(op=USub(), operand=Constant(value=1)), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_repr_excinfo_reprcrash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'repr.reprcrash is not None': Unsupported AST node: Attribute(value=Name(id='repr', ctx=Load()), attr='reprcrash', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_reprexcinfo_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == 'я'': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_toterminal_long
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_toterminal_long_missing_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_toterminal_long_incomplete_source
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_toterminal_long_filenames
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'msg == str(path)': Unknown symbol: msg
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_toterminal_value
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.get_write_msg(0) == 'some_value'': Unsupported AST node: Call(func=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='get_write_msg', ctx=Load()), args=[Constant(value=0)], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_format_excinfo
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'file.getvalue()': Unsupported AST node: Call(func=Attribute(value=Name(id='file', ctx=Load()), attr='getvalue', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_traceback_repr_style
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_exc_chain_repr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_exc_repr_chain_suppression
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tw_mock.lines[0] == ''': Unsupported AST node: Subscript(value=Attribute(value=Name(id='tw_mock', ctx=Load()), attr='lines', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: test_exc_chain_repr_cycle
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'out == expected_out': Unknown symbol: out
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: reraise_me
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'val is not None': Unknown symbol: val
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: raiseos
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'upframe is not None': Unknown symbol: upframe
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_excinfo.py
FUNCTION: bar
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_str_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(x) == '3'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='x', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_from_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source).startswith('def test_source_str_function() -> None:')': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[]), attr='startswith', ctx=Load()), args=[Constant(value='def test_source_str_function() -> None:')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_from_method
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source.lines == ['def test_method(self):', '    pass']': Unsupported AST node: Attribute(value=Name(id='source', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_from_lines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source.lines == ['a ', 'b', 'c']': Unsupported AST node: Attribute(value=Name(id='source', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_from_inner_function
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source).startswith('def f():')': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[]), attr='startswith', ctx=Load()), args=[Constant(value='def f():')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_strips
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source == Source()': Unknown symbol: source
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_strip_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'source2.lines == [' hello']': Unsupported AST node: Attribute(value=Name(id='source2', ctx=Load()), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstartingblock_singleline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getline_finally
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source).strip() == 'c(1)  # type: ignore'': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[]), attr='strip', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getfuncsource_dynamic
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(f_source).strip() == 'def f():\n    raise NotImplementedError()'': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='f_source', ctx=Load())], keywords=[]), attr='strip', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getfuncsource_with_multiline_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(Source(f)) == expected.rstrip()': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Name(id='Source', ctx=Load()), args=[Name(id='f', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_deindent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'deindent(['\tfoo', '\tbar']) == ['foo', 'bar']': Unsupported AST node: Call(func=Name(id='deindent', ctx=Load()), args=[List(elts=[Constant(value='\tfoo'), Constant(value='\tbar')], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_of_class_at_eof_without_newline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source).strip() == str(s2).strip()': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[]), attr='strip', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_fallback
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(src) == expected': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='src', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_findsource_fallback
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'src is not None': Unknown symbol: src
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_findsource
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'src is not None': Unknown symbol: src
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getfslineno
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(fspath, Path)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='fspath', ctx=Load()), Name(id='Path', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_code_of_object_instance_with_call
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''pass' in str(code.source())': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_oneline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'raise ValueError'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_comment_and_no_newline_at_end
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'end == 2': Unknown symbol: end
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_oneline_and_comment
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'raise ValueError'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_source_with_decorator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'textwrap.indent(str(Source(deco_mark)), '    ') + '\n' == src': Unsupported AST node: Call(func=Attribute(value=Name(id='textwrap', ctx=Load()), attr='indent', ctx=Load()), args=[Call(func=Name(id='str', ctx=Load()), args=[Call(func=Name(id='Source', ctx=Load()), args=[Name(id='deco_mark', ctx=Load())], keywords=[])], keywords=[]), Constant(value='    ')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_single_line_else
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'else: 3'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_single_line_finally
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'finally: 3'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_issue55
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(s) == '  round_trip("""\n""")'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='s', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'raise ValueError(\n    23\n)'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_semicolon
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == s.strip()': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_def_online
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'def func(): raise ValueError(42)'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_decorator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''@foo' in str(source)': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: XXX_test_expression_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(result) == "'''\n'''"': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='result', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstartingblock_multiline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getrange
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(x.lines) == 2': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='x', ctx=Load()), attr='lines', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getline
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == 'def f(x):'': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_len
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(self.source) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='self', ctx=Load()), attr='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_iter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(values) == 4': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='values', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_triple_quoted
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == source': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_within_constructs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(source) == 7': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_bug
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(source) == 6': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_bug2
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(source) == 9': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_ast_issue58
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'getstatement(2, source).lines == source.lines[2:3]': Unsupported AST node: Attribute(value=Call(func=Name(id='getstatement', ctx=Load()), args=[Constant(value=2), Name(id='source', ctx=Load())], keywords=[]), attr='lines', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_getstatementrange_out_of_bounds_py3
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'r == (1, 2)': Unknown symbol: r
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: deco_mark
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: deco_fixture
VERDICT: CONTRACT_VIOLATION
EVIDENCE: No model exists; contract is self-contradictory
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_body
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    raise ValueError'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_except_line
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'except Something:'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_except_body
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    raise IndexError(1)'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_else
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    raise KeyError()'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_body
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    raise ValueError'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_finally
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    raise IndexError(1)'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_body
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    y = 3'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_elif_clause
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == 'elif False:'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_elif
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    y = 5'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/code/test_source.py
FUNCTION: test_else
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(source) == '    y = 7'': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='source', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: path1
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path.join('samplefile').check()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='samplefile')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pypkgdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'pkg.pypkgpath() == pkg': Unsupported AST node: Call(func=Attribute(value=Name(id='pkg', ctx=Load()), attr='pypkgpath', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pypkgdir_unimportable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'subdir.pypkgpath() == subdir': Unsupported AST node: Call(func=Attribute(value=Name(id='subdir', ctx=Load()), attr='pypkgpath', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_isimportable
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not isimportable('')': Unsupported AST node: Call(func=Name(id='isimportable', ctx=Load()), args=[Constant(value='')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_homedir_from_HOME
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'local._gethomedir() == local(path)': Unsupported AST node: Call(func=Attribute(value=Name(id='local', ctx=Load()), attr='_gethomedir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_homedir_not_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'homedir is None': Unknown symbol: homedir
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_samefile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tmpdir.samefile(tmpdir)': Unsupported AST node: Call(func=Attribute(value=Name(id='tmpdir', ctx=Load()), attr='samefile', ctx=Load()), args=[Name(id='tmpdir', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_samefile_symlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p1.samefile(p2)': Unsupported AST node: Call(func=Attribute(value=Name(id='p1', ctx=Load()), attr='samefile', ctx=Load()), args=[Name(id='p2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir_single_arg
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tmpdir.listdir('hello')[0].basename == 'hello'': Unsupported AST node: Attribute(value=Subscript(value=Call(func=Attribute(value=Name(id='tmpdir', ctx=Load()), attr='listdir', ctx=Load()), args=[Constant(value='hello')], keywords=[]), slice=Constant(value=0), ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_mkdtemp_rootdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tmpdir.listdir() == [dtmp]': Unsupported AST node: Call(func=Attribute(value=Name(id='tmpdir', ctx=Load()), attr='listdir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_constructor_equality
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p == path1': Unknown symbol: p
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_eq_nonstring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p1 == p2': Unknown symbol: p1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_new_identical
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1 == path1.new()': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='new', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'strp.endswith('sampledir')': Unsupported AST node: Call(func=Attribute(value=Name(id='strp', ctx=Load()), attr='endswith', ctx=Load()), args=[Constant(value='sampledir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_normalized
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'strp.endswith('sampledir')': Unsupported AST node: Call(func=Attribute(value=Name(id='strp', ctx=Load()), attr='endswith', ctx=Load()), args=[Constant(value='sampledir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_noargs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1 == newpath': Unknown symbol: newpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_add_something
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p.check()': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_parts
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'par == [path1, path1.join('sampledir'), newpath]': Unknown symbol: par
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_common
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == path1': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_basename_checks
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.check(basename='sampledir')': Unsupported AST node: Call(func=Attribute(value=Name(id='newpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='basename', value=Constant(value='sampledir'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_basename
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.check(basename='sampledir')': Unsupported AST node: Call(func=Attribute(value=Name(id='newpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='basename', value=Constant(value='sampledir'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dirname
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.dirname == str(path1)': Unsupported AST node: Attribute(value=Name(id='newpath', ctx=Load()), attr='dirname', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dirpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.dirpath() == path1': Unsupported AST node: Call(func=Attribute(value=Name(id='newpath', ctx=Load()), attr='dirpath', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dirpath_with_args
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.dirpath('x') == path1.join('x')': Unsupported AST node: Call(func=Attribute(value=Name(id='newpath', ctx=Load()), attr='dirpath', ctx=Load()), args=[Constant(value='x')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_newbasename
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newbase.basename == 'samplefile2'': Unsupported AST node: Attribute(value=Name(id='newbase', ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_not_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not path1.join('does_not_exist').check()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='does_not_exist')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_exists
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('samplefile').check()': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='samplefile')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('sampledir').check(dir=1)': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fnmatch_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('samplefile').check(fnmatch='s*e')': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='samplefile')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='fnmatch', value=Constant(value='s*e'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_relto
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p.relto(path1) == p.sep.join(['sampledir', 'otherfile'])': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='relto', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_bestrelpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == '.'': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_relto_not_relative
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not l1.relto(l2)': Unsupported AST node: Call(func=Attribute(value=Name(id='l1', ctx=Load()), attr='relto', ctx=Load()), args=[Name(id='l2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('sampledir') in p': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir_fnmatchstring
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(p)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='p', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir_filter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('sampledir') in p': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir_sorted
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('sampledir') == p[0]': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_nofilter
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''sampledir' in lst': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_norecurse
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''sampledir' in lst': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_filterfunc_is_string
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lst)': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lst', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_ignore
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'list(p.visit(ignore=error.ENOENT)) == []': Unsupported AST node: Call(func=Name(id='list', ctx=Load()), args=[Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='visit', ctx=Load()), args=[], keywords=[keyword(arg='ignore', value=Attribute(value=Name(id='error', ctx=Load()), attr='ENOENT', ctx=Load()))])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_endswith
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.sep.join(['sampledir', 'otherfile']) in p': Unsupported AST node: Call(func=Attribute(value=Attribute(value=Name(id='path1', ctx=Load()), attr='sep', ctx=Load()), attr='join', ctx=Load()), args=[List(elts=[Constant(value='sampledir'), Constant(value='otherfile')], ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_cmp
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion '(path1 < path2) == ('samplefile' < 'samplefile2')': Unknown symbol: path2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_simple_read
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == 'samplefile\n'': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_div_operator
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath == newpath2': Unknown symbol: newpath
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ext
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.ext == '.ext'': Unsupported AST node: Attribute(value=Name(id='newpath', ctx=Load()), attr='ext', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_purebasename
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newpath.purebasename == 'samplefile'': Unsupported AST node: Attribute(value=Name(id='newpath', ctx=Load()), attr='purebasename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_multiple_parts
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(path1).endswith(dirname)': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[]), attr='endswith', ctx=Load()), args=[Name(id='dirname', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dotted_name_ext
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'ext == '.c'': Unknown symbol: ext
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_newext
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newext.basename == 'samplefile.txt'': Unsupported AST node: Attribute(value=Name(id='newext', ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_readlines
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'contents == ['samplefile\n']': Unknown symbol: contents
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_readlines_nocr
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'contents == ['samplefile', '']': Unknown symbol: contents
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('samplefile').check(file=1)': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='samplefile')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_not_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not path1.join('sampledir').check(file=1)': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_non_existent
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.join('sampledir.nothere').check(dir=0)': Unsupported AST node: Call(func=Attribute(value=Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='sampledir.nothere')], keywords=[]), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=0))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_size
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'url.size() > len('samplefile')': Unsupported AST node: Call(func=Attribute(value=Name(id='url', ctx=Load()), attr='size', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_mtime
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'url.mtime() > 0': Unsupported AST node: Call(func=Attribute(value=Name(id='url', ctx=Load()), attr='mtime', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_load
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'type(obj) is dict': Unsupported AST node: Call(func=Name(id='type', ctx=Load()), args=[Name(id='obj', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_filesonly
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''sampledir' not in p': Unsupported compare op: <class 'ast.NotIn'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_nodotfiles
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion ''sampledir' in p': Unsupported compare op: <class 'ast.In'>
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_sort
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'lst[:i] == sorted(lst[:i])': Unsupported AST node: Subscript(value=Name(id='lst', ctx=Load()), slice=Slice(upper=Name(id='i', ctx=Load())), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_endswith
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not chk(path1)': Unsupported AST node: Call(func=Name(id='chk', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'd.check()': Unsupported AST node: Call(func=Attribute(value=Name(id='d', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_dir_recursive_by_default
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'd.check()': Unsupported AST node: Call(func=Attribute(value=Name(id='d', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensure_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b.basename == '002'': Unsupported AST node: Attribute(value=Name(id='b', ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_mkdir_and_remove
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'new.check(dir=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='new', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_move_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'dest.check(dir=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='dest', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fspath_protocol_match_strpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.__fspath__() == path1.strpath': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='__fspath__', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fspath_func_match_strpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fspath(path1) == path1.strpath': Unsupported AST node: Call(func=Name(id='fspath', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fspath_fsencode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fsencode(path1) == fsencode(path1.strpath)': Unsupported AST node: Call(func=Name(id='fsencode', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_normpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'tmpdir.join('.') == tmpdir': Unsupported AST node: Call(func=Attribute(value=Name(id='tmpdir', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='.')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_dirpath_abs_no_abs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p.dirpath('/bar') == tmpdir.join('bar')': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='dirpath', ctx=Load()), args=[Constant(value='/bar')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_gethash
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'fn.computehash('md5') == md5(data).hexdigest()': Unsupported AST node: Call(func=Attribute(value=Name(id='fn', ctx=Load()), attr='computehash', ctx=Load()), args=[Constant(value='md5')], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_removes_readonly_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not readonly_file.check(exists=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='readonly_file', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='exists', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_removes_readonly_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not readonly_dir.check(exists=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='readonly_dir', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='exists', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_removes_dir_and_readonly_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not readonly_dir.check(exists=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='readonly_dir', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='exists', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_remove_routes_ignore_errors
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not lst[0]['ignore_errors']': Unsupported AST node: Subscript(value=Subscript(value=Name(id='lst', ctx=Load()), slice=Constant(value=0), ctx=Load()), slice=Constant(value='ignore_errors'), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_initialize_curdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(local()) == os.getcwd()': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Call(func=Name(id='local', ctx=Load()), args=[], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_chdir_gone
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1.chdir() is None': Unsupported AST node: Call(func=Attribute(value=Name(id='path1', ctx=Load()), attr='chdir', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_as_cwd
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'os.getcwd() == str(old)': Unsupported AST node: Call(func=Attribute(value=Name(id='os', ctx=Load()), attr='getcwd', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_as_cwd_exception
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'old == local()': Unknown symbol: old
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_tilde_expansion
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p == os.path.expanduser('~')': Unknown symbol: p
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_eq_hash_are_case_insensitive_on_windows
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'a == b': Unknown symbol: a
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_eq_with_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path1 == path2': Unknown symbol: path2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_eq_non_ascii_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path2 != path3': Unknown symbol: path2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_gt_with_strings
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'path3 > path2': Unknown symbol: path3
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_open_and_ensure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p.read_text(encoding='utf-8') == 'hello'': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='read_text', ctx=Load()), args=[], keywords=[keyword(arg='encoding', value=Constant(value='utf-8'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_write_and_ensure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p.read_text(encoding='utf-8') == 'hello'': Unsupported AST node: Call(func=Attribute(value=Name(id='p', ctx=Load()), attr='read_text', ctx=Load()), args=[], keywords=[keyword(arg='encoding', value=Constant(value='utf-8'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_normpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(new1) == str(new2)': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='new1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensure_filepath_withdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'newfile.check(file=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='newfile', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensure_filepath_withoutdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't == newfile': Unknown symbol: t
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensure_dirpath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't == newfile': Unknown symbol: t
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensure_non_ascii_unicode
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't == newfile': Unknown symbol: t
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_long_filenames
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'l2.read_text(encoding='utf-8') == 'foo'': Unsupported AST node: Call(func=Attribute(value=Name(id='l2', ctx=Load()), attr='read_text', ctx=Load()), args=[], keywords=[keyword(arg='encoding', value=Constant(value='utf-8'))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_depth_first
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lst) == 3': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lst', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_rec_fnmatch
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(lst) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Name(id='lst', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fnmatch_file_abspath
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b.fnmatch(os.sep.join('ab'))': Unsupported AST node: Call(func=Attribute(value=Name(id='b', ctx=Load()), attr='fnmatch', ctx=Load()), args=[Call(func=Attribute(value=Attribute(value=Name(id='os', ctx=Load()), attr='sep', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='ab')], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_sysfind
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.check(file=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fspath_protocol_other_class
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'py_path.check(endswith=str_path)': Unsupported AST node: Call(func=Attribute(value=Name(id='py_path', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='endswith', value=Name(id='str_path', ctx=Load()))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_sysfind_bat_exe_before
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x == h': Unknown symbol: x
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_sysfind_absolute
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.check(file=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_sysfind_multiple
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.basename == 'a'': Unsupported AST node: Attribute(value=Name(id='x', ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_make_numbered_dir_case
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(d1).lower() != str(d2).lower()': Unsupported AST node: Call(func=Attribute(value=Call(func=Name(id='str', ctx=Load()), args=[Name(id='d1', ctx=Load())], keywords=[]), attr='lower', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_make_numbered_dir_NotImplemented_Error
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.relto(tmpdir)': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='relto', ctx=Load()), args=[Name(id='tmpdir', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obj.x == 42': Unsupported AST node: Attribute(value=Name(id='obj', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_dir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'm.__name__ == 'hello_123'': Unsupported AST node: Attribute(value=Name(id='m', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_execfile_different_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obj.x == 42': Unsupported AST node: Attribute(value=Name(id='obj', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_a
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.result == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='result', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_b
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.stuff == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='stuff', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_c
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.value == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='value', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_d
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.value2 == 'got it'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='value2', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_and_import
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod1.__name__ == 'xxxpackage.module1'': Unsupported AST node: Attribute(value=Name(id='mod1', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_check_filepath_consistency
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'modname == name': Unknown symbol: modname
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_issue131_pyimport_on__init__
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'm1 == m2': Unknown symbol: m1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_ensuresyspath_append
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(root1) not in sys.path': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='root1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obj.x == 42': Unsupported AST node: Attribute(value=Name(id='obj', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_execfile_different_name
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'obj.x == 42': Unsupported AST node: Attribute(value=Name(id='obj', ctx=Load()), attr='x', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_pyimport_doesnt_use_sys_modules
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'mod.__name__ == 'file738jsk'': Unsupported AST node: Attribute(value=Name(id='mod', ctx=Load()), attr='__name__', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_path_comparison_lowercase_mixed
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't1 == t1': Unknown symbol: t1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_relto_with_mixed_case
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't1.relto(t2) == 'fiLe'': Unsupported AST node: Call(func=Attribute(value=Name(id='t1', ctx=Load()), attr='relto', ctx=Load()), args=[Name(id='t2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_allow_unix_style_paths
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 't1 == str(path1) + '\\a_path'': Unknown symbol: t1
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_fnmatch_file_abspath_posix_pattern_on_win32
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b.fnmatch(posixpath.sep.join('ab'))': Unsupported AST node: Call(func=Attribute(value=Name(id='b', ctx=Load()), attr='fnmatch', ctx=Load()), args=[Call(func=Attribute(value=Attribute(value=Name(id='posixpath', ctx=Load()), attr='sep', ctx=Load()), attr='join', ctx=Load()), args=[Constant(value='ab')], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_hardlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'filepath.stat().nlink == nlink + 1': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Name(id='filepath', ctx=Load()), attr='stat', ctx=Load()), args=[], keywords=[]), attr='nlink', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_are_identical
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'linkpath.readlink() == str(filepath)': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='readlink', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_isfile
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'linkpath.check(file=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='file', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_relative
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'linkpath.readlink() == 'file'': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='readlink', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_not_existing
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'not linkpath.check(link=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='link', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_relto_with_root
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'y[0] == str(path1)[1]': Unsupported AST node: Subscript(value=Name(id='y', ctx=Load()), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_visit_recursive_symlink
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'list(visitor) == [linkpath]': Unsupported AST node: Call(func=Name(id='list', ctx=Load()), args=[Name(id='visitor', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_isdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'linkpath.check(dir=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='dir', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_symlink_remove
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'linkpath.check(link=1)': Unsupported AST node: Call(func=Attribute(value=Name(id='linkpath', ctx=Load()), attr='check', ctx=Load()), args=[], keywords=[keyword(arg='link', value=Constant(value=1))])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_realpath_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'realpath.basename == 'file'': Unsupported AST node: Attribute(value=Name(id='realpath', ctx=Load()), attr='basename', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_owner
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stat.path == path1': Unsupported AST node: Attribute(value=Name(id='stat', ctx=Load()), attr='path', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_stat_helpers
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'stat1.isfile()': Unsupported AST node: Call(func=Attribute(value=Name(id='stat1', ctx=Load()), attr='isfile', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_stat_non_raising
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'res is None': Unknown symbol: res
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_atime
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'atime2 - atime1 <= duration': Unknown symbol: atime2
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_commondir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p1.common(p2) == path1': Unsupported AST node: Call(func=Attribute(value=Name(id='p1', ctx=Load()), attr='common', ctx=Load()), args=[Name(id='p2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_commondir_nocommon
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'p1.common(p2) == '/'': Unsupported AST node: Call(func=Attribute(value=Name(id='p1', ctx=Load()), attr='common', ctx=Load()), args=[Name(id='p2', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_to_root
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'len(str(root)) == 1': Unsupported AST node: Call(func=Name(id='len', ctx=Load()), args=[Call(func=Name(id='str', ctx=Load()), args=[Name(id='root', ctx=Load())], keywords=[])], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_root_to_root_with_no_abs
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'str(path1) == str(nroot)': Unsupported AST node: Call(func=Name(id='str', ctx=Load()), args=[Name(id='path1', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_copy_archiving
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'b.join(f.basename).stat().mode == newmode': Unsupported AST node: Attribute(value=Call(func=Attribute(value=Call(func=Attribute(value=Name(id='b', ctx=Load()), attr='join', ctx=Load()), args=[Attribute(value=Name(id='f', ctx=Load()), attr='basename', ctx=Load())], keywords=[]), attr='stat', ctx=Load()), args=[], keywords=[]), attr='mode', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_copy_stat_file
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'oldstat.mode == newstat.mode': Unsupported AST node: Attribute(value=Name(id='oldstat', ctx=Load()), attr='mode', ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_join_ensure
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.join(part) == y': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='join', ctx=Load()), args=[Name(id='part', ctx=Load())], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_listdir
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.listdir(part)[0] == y': Unsupported AST node: Subscript(value=Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='listdir', ctx=Load()), args=[Name(id='part', ctx=Load())], keywords=[]), slice=Constant(value=0), ctx=Load())
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_read_binwrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.read_binary() == part_utf8': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='read_binary', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_read_textwrite
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'x.read_binary() == part_utf8': Unsupported AST node: Call(func=Attribute(value=Name(id='x', ctx=Load()), attr='read_binary', ctx=Load()), args=[], keywords=[])
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/testing/_py/test_local.py
FUNCTION: test_default_encoding
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 's == part': Unknown symbol: s
--- END REPORT ---


--- PARADOX DISCOVERED ---
FILE: ../pytest/scripts/generate-gh-release-notes.py
FUNCTION: convert_rst_to_md
VERDICT: IMPLEMENTATION_FAILURE
EVIDENCE: Error in assertion 'isinstance(result, str)': Unsupported AST node: Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='result', ctx=Load()), Name(id='str', ctx=Load())], keywords=[])
--- END REPORT ---


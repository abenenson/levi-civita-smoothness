"""Fail-closed live verification controls; all compiler and Git calls are mocked."""
from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import verify_live as verify

SCRIPT = Path(__file__).with_name('verify_live.py')


def information(data):
    return json.dumps({'severity': 'information', 'data': data}) + '\n'


def fixture_repository(root):
    """Use 28 actual fixture sources to exercise the complete qualification path."""
    (root / 'scripts').mkdir(parents=True)
    (root / 'evidence').mkdir()
    for name in ['verify_live.py', 'verify_evidence.py',
                 'test_verify_live.py', 'test_verify_evidence.py']:
        shutil.copyfile(SCRIPT.with_name(name), root / 'scripts' / name)
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
    (root / 'lakefile.lean').write_text('import Lake\n')
    dep = {'name': 'mathlib', 'type': 'git',
           'url': 'https://github.com/leanprover-community/mathlib4',
           'rev': '56a005855ea17e0b0958f73ec801ae140b0a1679'}
    (root / 'lake-manifest.json').write_text(json.dumps({'packages': [dep]}))
    (root / '.lake/packages/mathlib').mkdir(parents=True)
    paths = ['MathlibExtensions.lean', 'LeviCivitaSmoothness.lean',
             'LeviCivitaSmoothness/Examples/MetricConsumer.lean']
    paths += [f'MathlibExtensions/Fixture{i}.lean' for i in range(25)]
    for name in paths:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        source = ('/- Copyright (c) 2026 Adam Benenson. -/\nmodule\n'
                  '/-! Fixture. -/\n@[expose] public section\n')
        if name == 'MathlibExtensions.lean':
            source += 'namespace Fixture\ntheorem identity : True := by trivial\nend Fixture\n'
        path.write_text(source)
    paths.sort(key=Path)
    config = {'source_count': 28, 'source_files': paths,
              'source_sha256': {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                                for name in paths},
              'configuration_sha256': {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                                      for name in ['lean-toolchain', 'lakefile.lean',
                                                   'lake-manifest.json']},
              'audit_imports': verify.AUDIT_IMPORTS, 'declarations': ['Fixture.identity'],
              'public_dependencies': {'mathlib': {'rev': dep['rev'], 'url': dep['url']}}}
    (root / 'evidence/live-inventory.json').write_text(json.dumps(config))
    return config


def fixture_git(command, **kwargs):
    if command[-2:] == ['rev-parse', 'HEAD']:
        return '56a005855ea17e0b0958f73ec801ae140b0a1679\n'
    if command[-3:] == ['ls-files', '-v', '-z']:
        return 'H Mathlib/Fixture.lean\0'
    if 'status' in command:
        return ''
    raise AssertionError(command)


class VerificationControls(unittest.TestCase):
    def test_clean_plain_and_json_information(self):
        verify.check_diagnostics('Build completed successfully.\n')
        verify.check_diagnostics(information('checked'), json_mode=True)

    def test_plain_json_and_zero_exit_diagnostics_fail_closed(self):
        for output in ['PANIC at kernel', 'panic: kernel', 'error: fixture',
                       'file.lean:3:2: warning: fixture', '{"severity":"error"',
                       information('warning: nested diagnostic')]:
            with self.subTest(output=output), self.assertRaises(AssertionError):
                verify.check_diagnostics(output)
        for obj in [{'severity': 'error', 'data': 'failure'},
                    {'severity': 'warning', 'data': 'failure'},
                    {'severity': 'information', 'data': 'PANIC at kernel'},
                    {'severity': 'fatal', 'data': 'failure'},
                    {'severity': 'information'}, {'error': 'failure'}, []]:
            with self.subTest(obj=obj), self.assertRaises(AssertionError):
                verify.check_diagnostics(json.dumps(obj), json_mode=True)
        with self.assertRaises(AssertionError):
            verify.check_diagnostics('unstructured output', json_mode=True)

    def test_public_multiline_imports_and_unsupported_syntax(self):
        source = ('/- import Ignored.Comment -/\nmodule\n'
                  'public import Mathlib.Data.Bool.Basic MathlibExtensions.Fixture\n'
                  'import\n Mathlib.Data.Nat.Basic\n LeviCivitaSmoothness\n'
                  '@[expose] public section\ndef s := "import Ignored.String"\n')
        self.assertEqual(verify.imported_modules(source),
                         ['Mathlib.Data.Bool.Basic', 'MathlibExtensions.Fixture',
                          'Mathlib.Data.Nat.Basic', 'LeviCivitaSmoothness'])
        for source in ['import «Unsupported»', 'import\nnamespace X\nend X']:
            with self.subTest(source=source), self.assertRaises(AssertionError):
                verify.imported_modules(source)

    def test_named_end_closes_intervening_sections_and_private_names_are_excluded(self):
        source = ('module\n@[expose] public section\nnamespace Outer\n'
                  'noncomputable section\nnamespace Inner\n'
                  'private theorem hidden : True := by trivial\n'
                  '@[simp] public theorem visible : True := by trivial\n'
                  'end\nend Outer\nnamespace Tail\ndef value := 1\n')
        self.assertEqual(verify.declarations(source), ['Outer.Inner.visible', 'Tail.value'])
        with self.assertRaises(AssertionError):
            verify.declarations('namespace A\nend B\n')

    def test_lint_probe_preserves_exact_module_source_and_full16_is_required(self):
        source = 'module\npublic import Mathlib.Data.Real.Basic\n@[expose] public section\n'
        probe = verify.lint_probe(source)
        self.assertEqual(probe.replace('import Mathlib.Tactic.Linter.Lint\n', '', 1)
                         .removesuffix('\n#lint+ docBlame docBlameThm\n'), source)
        clean = '-- All linting checks passed!\n-- Found 0 errors with 16 linters'
        verify.lint_result(information(clean))
        for output in ['', information(clean.replace('16 linters', '15 linters')),
                       information(clean.replace('Found 0 errors', 'Found 1 errors')),
                       information(clean.replace('All linting checks passed!', 'Incomplete'))]:
            with self.subTest(output=output), self.assertRaises(AssertionError):
                verify.lint_result(output)

    def test_axiom_free_format_and_exact_standard_three_ledger(self):
        names = ['A.first', 'A.second']
        clean = information("'A.first' depends on axioms: [Classical.choice, Quot.sound]")
        clean += information("'A.second' does not depend on any axioms")
        self.assertEqual(verify.axiom_reports(clean, names)['A.second'], [])
        for output in [clean.replace('Quot.sound', 'sorryAx'), clean.splitlines()[0],
                       clean + clean, clean.replace('A.second', 'A.other')]:
            with self.subTest(output=output), self.assertRaises(AssertionError):
                verify.axiom_reports(output, names)

    def test_optimized_python_refused(self):
        result = subprocess.run([sys.executable, '-O', str(SCRIPT), '--help'],
                                text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires enabled Python assertions', result.stderr)

    def test_real_inventory_is_all28_and_all118_public_names(self):
        root = verify.ROOT
        config = json.loads((root / 'evidence/live-inventory.json').read_text())
        verify.input_binding(root, config)
        actual = verify.source_declarations(root, config)
        self.assertEqual(len(actual), 118)
        self.assertEqual(actual, config['declarations'])
        self.assertEqual(config['audit_imports'], verify.AUDIT_IMPORTS)
        command = verify.cache_command(root)
        self.assertEqual(command[:4], ['lake', 'exe', 'cache', 'get'])
        self.assertIn(verify.LINT_IMPORT, command)
        self.assertTrue(all(name.startswith('Mathlib.') and '/' not in name
                            for name in command[4:]))

    def test_stale_artifacts_removed_and_unrelated_dependency_outputs_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            library = root / '.lake/build/lib/lean'
            library.mkdir(parents=True)
            dependency = root / '.lake/packages/mathlib/.lake/build/lib/lean/Fixture.olean'
            dependency.parent.mkdir(parents=True)
            dependency.write_bytes(b'dependency cache')
            unrelated = library / 'Unrelated.olean'
            unrelated.write_bytes(b'unrelated')
            stale = [library / ('Fixture' + suffix) for suffix in
                     ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean.hash', '.trace')]
            for path in stale:
                path.write_bytes(b'stale')
            removed = verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(set(removed), {str(path.relative_to(root)) for path in stale})
            self.assertTrue(all(not path.exists() for path in stale))
            self.assertEqual(dependency.read_bytes(), b'dependency cache')
            self.assertEqual(unrelated.read_bytes(), b'unrelated')

    def test_linked_artifact_directory_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            external = Path(temp) / 'external'
            external.mkdir()
            artifact = external / 'Fixture.olean'
            artifact.write_bytes(b'preserve')
            library = root / '.lake/build/lib/lean'
            library.parent.mkdir(parents=True)
            library.symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(AssertionError, 'Linked authored artifact directory'):
                verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(artifact.read_bytes(), b'preserve')

    def test_dependency_head_dirty_hidden_and_linked_states_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = fixture_repository(root)
            for marker in ['wrong-head', 'dirty', 'skip', 'assume']:
                def invalid_git(command, **kwargs):
                    if marker == 'wrong-head' and command[-2:] == ['rev-parse', 'HEAD']:
                        return 'a' * 40
                    if marker == 'dirty' and 'status' in command:
                        return ' M Mathlib/Fixture.lean'
                    if marker in {'skip', 'assume'} and 'ls-files' in command:
                        return ('S' if marker == 'skip' else 'h') + ' Mathlib/Fixture.lean\0'
                    return fixture_git(command)
                with self.subTest(marker=marker), \
                     patch.object(verify.subprocess, 'check_output', side_effect=invalid_git), \
                     self.assertRaises(AssertionError):
                    verify.dependency_binding(root, config)
            with patch.object(verify.subprocess, 'check_output', side_effect=fixture_git):
                verify.dependency_binding(root, config)
            dep = root / '.lake/packages/mathlib'
            dep.rename(dep.with_name('saved'))
            dep.symlink_to(dep.with_name('saved'), target_is_directory=True)
            with self.assertRaisesRegex(AssertionError, 'Linked/missing dependency'):
                verify.dependency_binding(root, config)

    def test_missing_source_and_inventory_drift_rejected_before_native(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = fixture_repository(root)
            path = root / 'MathlibExtensions/Fixture0.lean'
            path.unlink()
            with self.assertRaisesRegex(AssertionError, 'coverage'):
                verify.input_binding(root, config)

    def test_unlisted_authored_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = fixture_repository(root)
            (root / 'Unexpected.lean').write_text('module\n')
            with self.assertRaisesRegex(AssertionError, 'coverage'):
                verify.input_binding(root, config)

    def test_manifest_url_revision_and_pinned_mathlib_mismatches_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = fixture_repository(root)
            path = root / 'lake-manifest.json'
            original = path.read_text()
            for key, value in [('url', 'https://github.com/example/other'),
                               ('rev', 'a' * 40), ('type', 'path')]:
                manifest = json.loads(original)
                manifest['packages'][0][key] = value
                path.write_text(json.dumps(manifest))
                with self.subTest(key=key), self.assertRaises(AssertionError):
                    verify.dependency_binding(root, config)
            path.write_text(original)
            config['public_dependencies']['mathlib']['rev'] = 'a' * 40
            with self.assertRaisesRegex(AssertionError, 'Wrong pinned Mathlib'):
                verify.dependency_binding(root, config)

    def test_wrong_toolchain_and_omitted_public_name_fail_end_to_end(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            config = fixture_repository(root)
            config['declarations'] = []
            (root / 'evidence/live-inventory.json').write_text(json.dumps(config))
            evidence = Path(temp) / 'omitted-name'
            with self.assertRaisesRegex(AssertionError, 'Declaration inventory'):
                self.run_fixture(root, evidence, config)
            config['declarations'] = ['Fixture.identity']
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            config['configuration_sha256']['lean-toolchain'] = hashlib.sha256(
                (root / 'lean-toolchain').read_bytes()).hexdigest()
            (root / 'evidence/live-inventory.json').write_text(json.dumps(config))
            with self.assertRaises(AssertionError):
                self.run_fixture(root, Path(temp) / 'wrong-toolchain', config)

    def run_fixture(self, root, evidence, config, *, drift=None, build_error=False,
                    missing_artifact=False):
        def fake_run(command, **kwargs):
            if command == ['lake', 'env', 'lean', '--version']:
                output = 'Lean (version 4.35.0, fixture)'
            elif 'build' in command:
                self.assertEqual(len(command[4:]), 28)
                for relative in config['source_files']:
                    artifact = root / '.lake/build/lib/lean' / Path(relative).with_suffix('.olean')
                    self.assertFalse(artifact.exists(), 'Exact build consumed stale authored output')
                    if not missing_artifact:
                        artifact.parent.mkdir(parents=True, exist_ok=True)
                        artifact.write_bytes(b'fresh')
                output = information('error: synthetic zero-exit failure') if build_error else \
                    'Build completed successfully.'
            elif command[-1].endswith('axioms.lean'):
                source = Path(command[-1]).read_text()
                self.assertEqual(verify.imported_modules(source), verify.AUDIT_IMPORTS)
                output = information("'Fixture.identity' depends on axioms: [propext]")
                if drift:
                    path = root / drift
                    path.write_text(path.read_text() + '\n-- Changed during verification.\n')
            else:
                path = Path(command[-1])
                relative = path.relative_to(evidence / 'lint-sources')
                self.assertEqual(path.read_text(), verify.lint_probe((root / relative).read_text()))
                output = information('-- All linting checks passed! Found 0 errors with 16 linters')
            return SimpleNamespace(returncode=0, stdout=output)
        with patch.object(verify, '__file__', str(root / 'scripts/verify_live.py')), \
             patch.object(sys, 'argv', [str(SCRIPT), '--evidence-dir', str(evidence)]), \
             patch.object(verify.subprocess, 'run', side_effect=fake_run), \
             patch.object(verify.subprocess, 'check_output', side_effect=fixture_git), \
             redirect_stdout(io.StringIO()):
            verify.main()

    def test_mocked_full28_success_removes_cache_and_binds_final_inputs(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            config = fixture_repository(root)
            stale = root / '.lake/build/lib/lean/MathlibExtensions.olean'
            stale.parent.mkdir(parents=True)
            stale.write_bytes(b'invalid cached artifact')
            evidence = Path(temp) / 'evidence'
            self.run_fixture(root, evidence, config)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'passed')
            self.assertEqual(record['source_count'], 28)
            self.assertEqual(record['input_sha256'], record['final_input_sha256'])
            self.assertIn('.lake/build/lib/lean/MathlibExtensions.olean',
                          record['removed_authored_artifacts'])
            self.assertEqual(len(record['stages']), 31)

    def test_zero_exit_build_error_and_missing_fresh_artifact_fail_end_to_end(self):
        for keyword in ['build_error', 'missing_artifact']:
            with self.subTest(keyword=keyword), tempfile.TemporaryDirectory() as temp:
                root = Path(temp) / 'repo'
                config = fixture_repository(root)
                evidence = Path(temp) / 'evidence'
                with self.assertRaises(AssertionError):
                    self.run_fixture(root, evidence, config, **{keyword: True})
                self.assertEqual(json.loads((evidence / 'qualification.json').read_text())['status'],
                                 'failed')

    def test_source_configuration_verifier_and_inventory_mutation_fail_final_fence(self):
        for relative in ['MathlibExtensions.lean', 'lakefile.lean', 'scripts/verify_live.py',
                         'evidence/live-inventory.json']:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temp:
                root = Path(temp) / 'repo'
                config = fixture_repository(root)
                evidence = Path(temp) / 'evidence'
                with self.assertRaises(AssertionError):
                    self.run_fixture(root, evidence, config, drift=relative)
                self.assertEqual(json.loads((evidence / 'qualification.json').read_text())['status'],
                                 'failed')


if __name__ == '__main__':
    unittest.main()

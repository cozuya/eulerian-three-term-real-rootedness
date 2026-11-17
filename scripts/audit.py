#!/usr/bin/env python3
"""Audit build pins, source mechanisms, build output, and printed axiom dependencies.

This checks what the build used and what the theorems depend on; it does not check
mathematical truth.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TARGETS = {name: STANDARD for name in (
    'EulerianThreeTermVerification.real_rooted_iff',
    'EulerianThreeTermVerification.real_rooted_strong',
    'EulerianThreeTermVerification.degree_three_iff',
    'EulerianThreeTermVerification.degree_three_boundary',
    'EulerianThreeTermVerification.boundary_example',
    'EulerianThreeTermVerification.outside_example',
    'EulerianThreeTermVerification.sequence_exists',
    'EulerianRegion.eulerian_three_term_realRooted_iff',
    "EulerianRegion.eulerian_three_term_realRooted_iff'",
    'EulerianRegion.primaryClaim_holds',
    'EulerianRegion.combination_splits',
    'EulerianRegion.combination_three_splits_iff',
    'EulerianRegion.combination_splits_of_branch',
    'EulerianRegion.combination_splits_b_zero_even',
    'EulerianRegion.Cay_succ_eq_homog',
    'EulerianRegion.residue_pos',
    'EulerianRegion.positive_partial_fractions',
    'EulerianRegion.cor_3_2',
    'EulerianRegion.lemma_4_1',
    'EulerianRegion.central_identity',
    'EulerianRegion.Phat_signPattern',
    'EulerianRegion.Rzero_signPattern',
    'EulerianRegion.splits_of_homog',
)}
LEAN_FILES = ('EulerianRegion.lean', 'Verification.lean') + tuple(
    'EulerianRegion/' + name + '.lean' for name in (
        'BoundaryZero', 'Cayley', 'Central', 'Definitions', 'MainTheorem', 'PartialFractions',
        'Residue', 'RootCount', 'Sanity', 'Separator', 'Statement', 'Sufficiency'))
# Attributes are rejected except `@[simp]` (simp lemma sets) and `@[expose]` (module-system
# visibility of definition bodies); neither can change what the kernel checks.
FORBIDDEN = re.compile(r'\b(sorry|sorryAx|admit|axiom|unsafe|implemented_by|extern|csimp|'
                       r'opaque|native_decide|decide_cbv|ofReduceBool|skipKernelTC|debug|'
                       r'notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|'
                       r'elab|elab_rules|instance|attribute|export)\b|@\[(?!(?:simp|expose)\])')


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def strip_comments(text):
    """Remove `--` line comments and nested `/- ... -/` block comments and docstrings."""
    result, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('-/', i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    require(depth == 0, 'Unterminated block comment')
    return ''.join(result)


def manifest_hashes():
    entries = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed source digest')
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), 'Source path escapes project')
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, 'Source digest mismatch: ' + name)
        require(name not in entries, 'Duplicate source digest: ' + name)
        entries[name] = actual
    return entries


def axiom_reports(transcript):
    require(not re.search(r'\b(?:warning|error):', transcript),
            'Compiler warning or error in the restatement check')
    records = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", transcript, flags=re.M)
    found = {}
    for name, axioms in records:
        require(name in TARGETS, 'Unexpected axiom report: ' + name)
        require(name not in found, 'Duplicate axiom report: ' + name)
        deps = {a.strip() for a in axioms.split(',') if a.strip()}
        require(deps == TARGETS[name], 'Unexpected axiom dependencies: ' + name)
        found[name] = sorted(deps)
    require(set(found) == set(TARGETS), 'Missing axiom reports: ' +
            ', '.join(sorted(set(TARGETS) - set(found))))
    return found


mode = sys.argv[1]
if mode == 'pins':
    pin = json.loads((ROOT / 'TOOLCHAIN.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() ==
            'leanprover/lean4:v' + pin['lean_version'], 'Toolchain file')
    require(output('lean', '--short-version') == pin['lean_version'], 'Lean version')
    require(output('lean', '--githash') == pin['lean_commit'], 'Lean commit')
    require(output('lake', '--version').startswith('Lake version ' + pin['lake_version']),
            'Lake version')
    require(f'rev = "{pin["mathlib_commit"]}"' in (ROOT / 'lakefile.toml').read_text(),
            'lakefile mathlib revision')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    require(packages['mathlib']['rev'] == pin['mathlib_commit'], 'mathlib revision')
    require(packages['mathlib']['inputRev'] == pin['mathlib_commit'], 'mathlib input revision')
    for package in manifest['packages']:
        require(package['type'] == 'git' and
                re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                'Unpinned dependency: ' + package['name'])
        require(output('git', '-C', '.lake/packages/' + package['name'],
                       'rev-parse', 'HEAD') == package['rev'],
                'Dependency checkout: ' + package['name'])
        require(output('git', '-C', '.lake/packages/' + package['name'],
                       'status', '--porcelain', '--untracked-files=no') == '',
                'Modified dependency checkout: ' + package['name'])
    mathlib_toolchain = ROOT / '.lake/packages/mathlib/lean-toolchain'
    require(mathlib_toolchain.read_text().strip() == 'leanprover/lean4:v' + pin['lean_version'],
            'Dependency toolchain: mathlib')
    print(f'PASS: Lean, Lake, toolchain file, mathlib, and all {len(packages)} locked '
          f'dependencies agree and are unmodified.')
elif mode == 'sources':
    paths = sorted(ROOT / name for name in LEAN_FILES)
    found = sorted(p for p in ROOT.rglob('*.lean')
                   if not any(part in ('.lake', '.tools', '.build') for part in p.relative_to(ROOT).parts))
    require(found == paths, 'Unexpected Lean file inventory: ' +
            ', '.join(p.relative_to(ROOT).as_posix() for p in found))
    for path in paths:
        name = path.relative_to(ROOT).as_posix()
        match = FORBIDDEN.search(strip_comments(path.read_text()))
        require(match is None, f'Forbidden mechanism {match and match.group(0)!r} in {name}')
    print(f'PASS: {len(paths)} Lean files; outside comments, no sorry, admit, axiom declarations, '
          f'native_decide, unsafe code, implemented_by, extern, csimp, opaque, kernel-check '
          f'options, instances, notation, macros, or attributes other than @[simp] and @[expose].')
elif mode == 'build':
    log = Path(sys.argv[2]).read_text()
    require(not re.search(r'(?m)^(?:warning|error)\b|⚠|✖|declaration uses .sorry.', log),
            'Build log contains a warning or error')
    require('Build completed successfully' in log, 'Build did not complete')
    print('PASS: build completed with no warnings or errors.')
elif mode == 'axioms':
    transcript = Path(sys.argv[2]).read_text()
    found = axiom_reports(transcript)
    for name in sorted(found):
        print('PASS:', name, 'uses exactly', ', '.join(found[name]))
    print('PASS: no sorryAx, native_decide axiom, or project-specific axiom in any audited theorem.')
elif mode == 'hashes':
    for name, digest in manifest_hashes().items():
        print(digest, name)
elif mode == 'record':
    exit_code = int(sys.argv[2])
    commit = None
    try:
        git_root = Path(subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'], cwd=ROOT, text=True,
            stderr=subprocess.DEVNULL).strip()).resolve()
        if git_root == ROOT:
            commit = output('git', 'rev-parse', 'HEAD')
    except subprocess.CalledProcessError:
        pass
    dirty = output('git', 'status', '--porcelain', '--untracked-files=no') != '' if commit else None
    actual_axioms = axiom_reports((ROOT / '.build/kernel-check.log').read_text()) if exit_code == 0 else None
    data = {
        'verification_exit_code': exit_code,
        'status': 'PASS' if exit_code == 0 else 'FAIL',
        'started_utc': sys.argv[3],
        'finished_utc': sys.argv[4],
        'repository_commit_at_run': commit,
        'tracked_worktree_dirty': dirty,
        'identity_note': 'Precommit verification is identified by source hashes; timestamps do not establish priority.',
        'trust_note': 'All audited theorems use only propext, Classical.choice and Quot.sound; '
                      'they are checked by the Lean kernel, including the Mathlib lemmas they use.',
        'leanchecker_replay': sys.argv[5] == '1',
        'toolchain': json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
        'source_sha256': manifest_hashes(),
        'audited_theorems': sorted(TARGETS),
        'expected_axioms': {k: sorted(v) for k, v in sorted(TARGETS.items())},
        'axiom_dependencies': actual_axioms,
        'transcript': 'verification.log',
        'theorem_types_and_axioms': 'kernel-check.log',
    }
    (ROOT / '.build/verification.json').write_text(json.dumps(data, indent=2) + '\n')
    print('Wrote .build/verification.json')
else:
    raise SystemExit('Unknown audit mode: ' + mode)

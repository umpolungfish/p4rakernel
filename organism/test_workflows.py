#!/usr/bin/env python3
"""Exercise the documented organism CLI, retained continuation and growth."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--runtime', required=True, type=Path, help='output of verify_organism.py')
parser.add_argument('--out', required=True, type=Path, help='fresh directory for complete test returns')
parser.add_argument('--long-steps', type=int, default=32)
options = parser.parse_args()
runtime = options.runtime.resolve()
out = options.out.resolve()
if out.exists():
    raise SystemExit(f'Choose a fresh output directory: {out}')
if options.long_steps < 12:
    raise SystemExit('--long-steps must be at least 12')
out.mkdir(parents=True)
records = []


def call(name, command, expected=0, env=None):
    start = time.monotonic()
    result = subprocess.run([str(x) for x in command], cwd=ROOT, env=env, capture_output=True, timeout=180)
    (out / (name + '.stdout')).write_bytes(result.stdout)
    (out / (name + '.stderr')).write_bytes(result.stderr)
    records.append(dict(name=name, command=[str(x) for x in command], exit_code=result.returncode,
                        seconds=time.monotonic() - start))
    (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
    assert (result.returncode == 0) == (expected == 0), (name, result.returncode, result.stderr[-2000:])
    print(name, result.returncode, flush=True)
    return result


def validate(value, source, requested, neural):
    assert value['source'] == source
    completed = value['continuation']
    assert 0 <= completed <= requested
    actions, nodes = value['actions'], value['nodes']
    assert len(actions) == 6 * completed and len(nodes) == len(actions) + 1
    assert len(set(value['frontier'])) == len(value['frontier'])
    consumed = {a['tip'] for a in actions}
    assert not consumed.intersection(value['frontier'])
    assert set(value['frontier']) | consumed == set(range(len(nodes)))
    assert all(n['source'] == source and n['boundary'] == 8 for n in nodes)
    assert nodes[0]['articulation'] == ([0] if completed == 0 else [0, 1, 3, 7, 15])
    assert all(n['articulation'] == [0, 1, 3, 7, 15] for n in nodes[1:])
    operations = 0
    initial_optimizer = None
    for index, action in enumerate(actions):
        assert nodes[index + 1]['parent'] == action['tip']
        assert nodes[action['tip']]['state'] == action['before']
        assert nodes[index + 1]['state'] == action['after']
        assert len(action['judgment_trace']) == len(action['judge_before'])
        assert len(action['model_probes']) == len(action['model_ancestry'])
        for prior in action['model_ancestry']:
            assert prior < index
            assert actions[prior]['rule'] == action['rule'] and actions[prior]['before'] == action['before']
        operations += len(action['program_before'])
        if neural:
            assert len(action['neural_operations']) == len(action['program_before'])
            carried = action['before']
            for operation in action['neural_operations']:
                assert operation['input'] == carried
                assert operation['optimizer_after'] == operation['optimizer_before'] + 1
                if initial_optimizer is None:
                    initial_optimizer = operation['optimizer_before']
                assert all(math.isfinite(x) for x in operation['rails_before'] + operation['rails_after'])
                for bit, evidence in enumerate(operation['membership_evidence']):
                    proposal = (operation['proposal_after'] >> bit) & 1
                    target = (operation['expected'] >> bit) & 1
                    assert evidence == [int(bool(proposal or target)), int(not proposal or not target)]
                    assert evidence in [[1, 0], [0, 1], [1, 1]]
                carried = operation['proposal_after']
            assert carried == action['after']
        else:
            assert action['neural_operations'] == []
    assert all(c in [[1, 0], [0, 1]] for c in value['clock']['cells'])
    assert sum(c[0] << i for i, c in enumerate(value['clock']['cells'])) == operations
    if neural:
        learner = value['learner']
        assert learner and learner['backend'] == 'VGI-native-retained'
        assert len(learner['parameters']) == len(learner['adam_m']) == len(learner['adam_v'])
        assert all(math.isfinite(x) for key in ['parameters', 'adam_m', 'adam_v'] for x in learner[key])
        if operations:
            assert learner['optimizer_clock'] == initial_optimizer + operations
    else:
        assert value['learner'] is None
    return dict(source=source, requested_steps=requested, completed_steps=completed, actions=len(actions),
                nodes=len(nodes), operations=operations,
                model_probes=sum(len(a['model_probes']) for a in actions),
                held_coordinates=sum(e == [1, 1] for a in actions for n in a['neural_operations'] for e in n['membership_evidence']),
                judge_program=value['judge_program'], generator_program=value['generator_program'])


binary = runtime / 'organism'
library = runtime / 'vgi_organism.so'
measurements = []
for source in range(16):
    result = call(f'neural_source_{source:02}', [binary, '4', str(source), library])
    measurements.append(validate(json.loads(result.stdout), source, 4, True))

zero = call('initial_neural_body', [binary, '0', '8', library])
validate(json.loads(zero.stdout), 8, 0, True)
exact = call('exact_native_control', [binary, '12', '8'])
measurements.append(validate(json.loads(exact.stdout), 8, 12, False))
repeat = call('documented_manual_run', [binary, '12', '8', library])
validate(json.loads(repeat.stdout), 8, 12, True)
assert repeat.stdout == (runtime / 'return.json').read_bytes(), 'fresh-process repeat differs from its complete initial state'
longer = call('longer_growth', [binary, str(options.long_steps), '8', library])
measurements.append(validate(json.loads(longer.stdout), 8, options.long_steps, True))

for name, arguments, message in [
    ('negative_steps', ['-1'], 'steps must be a natural number'),
    ('invalid_steps', ['word'], 'steps must be a natural number'),
    ('out_of_range_source', ['1', '16'], 'source-mask must be 0..15'),
    ('negative_source', ['1', '-1'], 'source-mask must be 0..15'),
    ('extra_arguments', ['1', '8', str(library), 'extra'], 'usage:'),
    ('missing_library', ['1', '8', str(out / 'absent.so')], 'cannot open shared object file')]:
    result = call(name, [binary] + arguments, expected=1)
    assert message in (result.stdout + result.stderr).decode(errors='replace'), name

prior_receipt = (runtime / 'receipt.json').read_bytes()
reuse = call('reject_receipt_overwrite', ['python3', ROOT / 'tests/kernel_features/verify_organism.py', '--out', runtime], expected=1)
assert b'already exists' in reuse.stdout + reuse.stderr
assert (runtime / 'receipt.json').read_bytes() == prior_receipt

environment = os.environ.copy()
environment['LEAN_PATH'] = str(runtime)
call('continuation_compile', [ROOT / 'build/stage1/bin/lean', '-c', out / 'continuation.c',
                             ROOT / 'tests/kernel_features/OrganismContinuation.lean'], env=environment)
call('continuation_link', [ROOT / 'build/stage1/bin/leanc', runtime / 'NativeDialetheicOrganism.c',
                          out / 'continuation.c', '-o', out / 'continuation'])
continuation = json.loads(call('retained_continuation', [out / 'continuation', library]).stdout)

report = dict(status='passed', source_masks_tested=16, deterministic_complete_return=True,
              continuation=continuation, measurements=measurements, invalid_input_checks=6,
              prior_receipt_preserved=True,
              images={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [binary, library]},
              sources={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                       [Path(__file__).resolve(), ROOT / 'tests/kernel_features/OrganismContinuation.lean']})
(out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ['sources', 'images', 'measurements']}), flush=True)

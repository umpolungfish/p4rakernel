#!/usr/bin/env python3
"""Exercise the real organism CLI, including stop and rebuilding a live run."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

WORK = Path(__file__).resolve().parents[2]
CLI = WORK / 'organism'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    records = []

    def call(label, *arguments, expected=0):
        command = [str(CLI), *map(str, arguments)]
        result = subprocess.run(command, cwd=WORK, capture_output=True)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        (out / (label + '.stderr')).write_bytes(result.stderr)
        records.append({'label': label, 'command': command, 'exit_code': result.returncode})
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        assert result.returncode == expected, (label, result.stderr.decode())
        return result.stdout

    source = WORK / 'p4rakernel/measurements/organism_factor_20261025/production/inputs/target128.N.txt'
    control = WORK / 'p4rakernel/measurements/organism_toroidal_division_20261025/logical_reentry_inputs/control128.N.txt'
    call('help', '--help')
    for label in ['stop', 'restart']:
        run = out / (label + '_initial')
        with (out / (label + '_initial.stdout')).open('wb') as stdout, (out / (label + '_initial.stderr')).open('wb') as stderr:
            process = subprocess.Popen([str(CLI), 'factor', '--source', str(source), '--out', str(run), '--seconds', '600', '--json'], cwd=WORK, stdout=stdout, stderr=stderr)
            deadline = time.monotonic() + 30
            while not (run / 'active.json').exists():
                assert process.poll() is None, 'Factor exited before exposing a live handle'
                assert time.monotonic() < deadline, 'Missing live handle'
                time.sleep(.02)
            before = json.loads(call(label + '_live', 'status', run, '--json'))
            assert before['status'] == 'running' and before['live_pid']
            if label == 'stop':
                call('stop_command', 'stop', run)
            else:
                returned = json.loads(call('restart_command', 'restart', run, '--out', out / 'restarted', '--seconds', '600', '--json'))
                assert returned['verified'] and returned['logical_reentry_return_verified']
                assert returned['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()
                assert returned['command'][0] != before['command'][0], 'Restart must select a fresh build'
            assert process.wait(timeout=15) == 3
        ended = json.loads(call(label + '_terminal', 'status', run, '--json'))
        assert ended['status'] == 'stopped' and ended['exit_code'] < 0
    restarted = out / 'restarted'
    result = json.loads(call('control', 'factor', '--source', control, '--out', out / 'control', '--seconds', '600', '--json'))
    assert result['verified'] and result['logical_reentry_return_verified']
    trace = json.loads(call('trace', 'inspect', restarted, '--trace', '--json'))
    assert trace and any(e['operation'] == 'conflation-return' for e in trace)
    stats = json.loads(call('stats', 'inspect', restarted, '--stats'))
    assert isinstance(stats, dict)
    growth = json.loads(call('growth', 'grow', '--steps', '2', '--out', out / 'growth', '--json'))
    assert growth['status'] == 'completed' and growth['completed_steps'] == 2
    receipt = {'verified': True, 'coverage': ['live PID', 'stop', 'live restart', 'rebuild', 'N-only target/control closure', 'logical trace', 'phase stats', 'native VGI growth'], 'restarted': json.loads((restarted / 'receipt.json').read_text()), 'control': result}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()

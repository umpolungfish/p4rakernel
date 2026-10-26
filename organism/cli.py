#!/usr/bin/env python3
"""Build, run and inspect the native dialetheic organism."""
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

KERNEL = Path(__file__).resolve().parents[1]
WORK = KERNEL.parent
HOME = KERNEL / 'measurements/organism_cli'
CURRENT = HOME / 'current_runtime.json'


def read(path):
    return json.loads(Path(path).read_text())


def stamp():
    return datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')


def fresh(kind):
    path = HOME / kind / stamp()
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def native_processes():
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():
            continue
        try:
            command = [s.decode() for s in (proc / 'cmdline').read_bytes().split(b'\0') if s]
            if command and Path(command[0]).name in ['organism-factor', 'organism'] and str(KERNEL) in command[0]:
                ticks = (proc / 'stat').read_text().rsplit(')', 1)[1].split()[19]
                yield int(proc.name), command, ticks
        except (OSError, UnicodeError, IndexError):
            continue


@contextmanager
def exclusive(wait=0):
    HOME.mkdir(parents=True, exist_ok=True)
    with (HOME / 'operation.lock').open('a+') as lock:
        deadline = time.monotonic() + wait
        while True:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise RuntimeError('An organism command is active. Use status or restart.')
                time.sleep(.1)
        try:
            active = list(native_processes())
            if active:
                raise RuntimeError(f'Organism PID {active[0][0]} is active. Stop it before building or starting another run.')
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def runtime(path=None):
    if path:
        selected = Path(path).expanduser().resolve()
    elif CURRENT.exists():
        selected = Path(read(CURRENT)['runtime'])
    else:
        candidates = list(KERNEL.glob('measurements/*/runtime*/build.json'))
        candidates += list((HOME / 'builds').glob('*/build.json'))
        candidates = [p for p in candidates if (p.parent / 'organism-factor').exists()]
        if not candidates:
            raise RuntimeError('No organism runtime found. Run: ./organism build')
        selected = max(candidates, key=lambda p: p.stat().st_mtime).parent
    manifest = read(selected / 'build.json')
    for name in ['organism-factor', 'factor_bridge.so', 'vgi_organism.so']:
        image = selected / name
        expected = manifest['images'].get(str(image))
        if not expected or hashlib.sha256(image.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'Runtime image binding failed: {image}. Run ./organism build.')
    return selected


def build(out=None, stream=None):
    destination = Path(out).expanduser().resolve() if out else fresh('builds')
    if destination.exists():
        raise RuntimeError(f'Preserving existing build: {destination}. Choose a fresh --out.')
    # Restored source timestamps previously allowed stale libraries to survive.
    subprocess.run(['cargo', 'clean', '--release', '--target', 'x86_64-unknown-linux-gnu',
                    '-p', 'vox', '-p', 'organism-factor-bridge'],
                   cwd=KERNEL / 'organism/factor_bridge', stdout=stream, check=True)
    subprocess.run([sys.executable, str(KERNEL / 'organism/build_factor.py'),
                    '--out', str(destination)], cwd=WORK, stdout=stream, check=True)
    runtime(destination)
    manifest = read(destination / 'build.json')
    for source, digest in manifest['sources'].items():
        original = Path(source)
        if hashlib.sha256(original.read_bytes()).hexdigest() != digest:
            raise RuntimeError(f'Source changed during build: {source}')
        target = destination / 'source' / original.relative_to(WORK)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(original.read_bytes())
    write(CURRENT, {'runtime': str(destination), 'build_receipt': str(destination / 'build.json')})
    print(f'Runtime ready: {destination}', file=stream or sys.stdout, flush=True)
    return destination


def runs():
    paths = list((HOME / 'runs').glob('*/active.json'))
    paths += list(KERNEL.glob('measurements/organism_*/*/active.json'))
    return sorted(set(p.parent for p in paths), key=lambda p: (p / 'active.json').stat().st_mtime, reverse=True)


def run_path(value=None):
    if value:
        path = Path(value).expanduser().resolve()
        return path.parent if path.is_file() else path
    found = runs()
    if not found:
        raise RuntimeError('No organism runs found. Run: ./organism factor --source FILE')
    return found[0]


def state(path):
    receipt = path / 'receipt.json'
    if receipt.exists():
        report = read(receipt)
        status = (report['status'] if report.get('application') == 'native-growth' else
                  'closed' if report.get('verified') else
                  'timeout' if report.get('timeout') else
                  'stopped' if report.get('exit_code', 0) < 0 else report.get('boundary', 'failed'))
        return {**report, 'status': status, 'run': str(path)}
    active = read(path / 'active.json')
    matches = [(pid, ticks) for pid, command, ticks in native_processes()
               if command == active.get('command')]
    # New runs have an exact start-time identity. Legacy namespace-local PIDs
    # are never used by themselves as evidence that a process is running.
    expected = active.get('process_start_ticks')
    if expected is not None:
        matches = [(pid, ticks) for pid, ticks in matches if ticks == expected]
    else:
        boot = next(int(line.split()[1]) for line in Path('/proc/stat').read_text().splitlines() if line.startswith('btime '))
        matches = [(pid, ticks) for pid, ticks in matches
                   if abs(boot + int(ticks) / os.sysconf('SC_CLK_TCK') - (path / 'active.json').stat().st_mtime) < 5]
    return {**active, 'run': str(path), 'status': 'running' if len(matches) == 1 else 'unverified',
            'live_pid': matches[0][0] if len(matches) == 1 else None}


def summary(report):
    text = f"{report['status']}: {report['run']}"
    if report.get('live_pid'):
        text += f"\nPID {report['live_pid']}; limit {report['execution_limit_seconds']} seconds"
    if 'process_seconds' in report:
        text += f"\nElapsed {report['process_seconds']:.3f}s"
    if report.get('verified'):
        text += f"\n{report['p']} × {report['q']} (exact product and return verified)"
    if 'logical_reentries' in report:
        text += f"\nLogical re-entries {report['logical_reentries']}; C returns {report['conflation_returns']}"
    if report.get('paired_learning_context_verified'):
        text += f"\nVGI paired-state frames {report['task_context_records']}; exact context tokens {report['task_context_tokens']} verified"
    if report.get('root_sign_transport_verified'):
        text += f"\nRoot-sign actions {report['root_sign_actions']}; changed polynomials {report['root_sign_changed_polynomials']}; inverse/source checks verified"
    if report.get('application') == 'native-growth':
        text += f"\nGrowth steps {report.get('completed_steps', 0)}; source mask {report['source_mask']}; VGI={report['vgi']}"
    if report['status'] == 'unverified':
        text += '\nNo terminal receipt; a matching live process is not visible from this PID namespace.'
    return text


def stop(path, stream=None):
    report = state(path)
    if report['status'] == 'running':
        os.kill(report['live_pid'], signal.SIGTERM)
        for _ in range(100):
            if (path / 'receipt.json').exists() or not any(pid == report['live_pid'] for pid, _, _ in native_processes()):
                break
            time.sleep(.1)
        print(f"Stopped organism PID {report['live_pid']}", file=stream or sys.stdout, flush=True)
    elif report['status'] == 'unverified':
        raise RuntimeError('Cannot identify this run safely from this PID namespace. Use the host terminal that launched it.')
    else:
        print(f"Run already ended: {report['status']}", file=stream or sys.stdout, flush=True)
    return report


def factor(args, selected=None, source_override=None):
    selected = selected or runtime(args.runtime)
    out = Path(args.out).expanduser().resolve() if args.out else fresh('runs')
    if out.exists():
        raise RuntimeError(f'Preserving existing run: {out}. Choose a fresh --out.')
    out.parent.mkdir(parents=True, exist_ok=True)
    source = Path(source_override or args.source).expanduser().resolve() if source_override or args.source else None
    raw = source.read_text().strip() if source else args.N
    if not raw or any(c not in '0123456789' for c in raw):
        raise RuntimeError('Supply N as a decimal integer or an N-only decimal file.')
    n = int(raw)
    if n.bit_length() < 128 or not n & 1:
        raise RuntimeError('The native toroidal task requires an odd N of at least 128 bits.')
    if source is None:
        source = out.with_name(out.name + '.N.txt')
        source.write_text(str(n) + '\n')
    write(out.with_name(out.name + '.configuration.json'),
          {'runtime': str(selected), 'source': str(source), 'source_bits': n.bit_length(),
           'seconds': args.seconds, 'GFE_WORKERS': args.workers, 'input_boundary': 'N alone'})
    stream = sys.stderr if args.json else sys.stdout
    print(f'Organism: {n.bit_length()}-bit N; limit {args.seconds}s; shared workers {args.workers}\nRun: {out}', file=stream, flush=True)
    env = os.environ.copy();env['GFE_WORKERS'] = str(args.workers)
    command = [sys.executable, str(KERNEL / 'organism/run_factor.py'), '--runtime', str(selected),
               '--source', str(source), '--out', str(out), '--seconds', str(args.seconds)]
    with out.with_name(out.name + '.runner.stdout').open('wb') as stdout, out.with_name(out.name + '.runner.stderr').open('wb') as stderr:
        process = subprocess.Popen(command, cwd=WORK, env=env, stdout=stdout, stderr=stderr)
        announced = False
        try:
            while process.poll() is None:
                if not announced and (out / 'active.json').exists():
                    active = read(out / 'active.json')
                    if active.get('status') == 'running_at_record':
                        print(f"Native PID {active['pid']}", file=stream, flush=True)
                        announced = True
                time.sleep(.2)
        except KeyboardInterrupt:
            if (out / 'active.json').exists():
                current = state(out)
                if current.get('live_pid'):
                    os.kill(current['live_pid'], signal.SIGTERM)
            try:process.wait(timeout=10)
            except subprocess.TimeoutExpired:process.kill();process.wait()
            return 130
    if not (out / 'receipt.json').exists():
        raise RuntimeError(f'Runner failed; read {out.with_name(out.name + ".runner.stderr")}')
    report = state(out)
    print(json.dumps(report, indent=2) if args.json else summary(report), flush=True)
    return 0 if report.get('verified') else 3


def check(component, out=None):
    destination = Path(out).expanduser().resolve() if out else fresh('checks')
    destination.mkdir(parents=True, exist_ok=False)
    selections = {'arithmetic': 'belnap_word::', 'roots': 'root_reentry::',
                  'phase': 'square_fold::phase::tests::', 'reentry': 'toroidal_division::'}
    records = []
    for name, selection in selections.items():
        if component not in ['all', name]:
            continue
        command = ['cargo', 'test', '--offline', '--release', '--target', 'x86_64-unknown-linux-gnu', '--lib', selection, '--', '--nocapture']
        result = subprocess.run(command, cwd=WORK / 'Vox', capture_output=True)
        (destination / f'{name}.stdout').write_bytes(result.stdout)
        (destination / f'{name}.stderr').write_bytes(result.stderr)
        records.append({'command': command, 'exit_code': result.returncode})
        write(destination / 'commands.json', records)
        print(f"{name}: {'passed' if result.returncode == 0 else 'failed'}", flush=True)
        if result.returncode:
            raise RuntimeError(f'Check failed; read {destination / (name + ".stderr")}')
    if component in ['all', 'native', 'reentry', 'continuation']:
        subprocess.run([sys.executable, str(KERNEL / 'tests/kernel_features/verify_organism.py'),
                        '--out', str(destination / 'native')], cwd=WORK, check=True)
    if component in ['all', 'continuation']:
        subprocess.run([sys.executable, str(KERNEL / 'organism/test_workflows.py'),
                        '--runtime', str(destination / 'native'), '--out', str(destination / 'continuation')],
                       cwd=WORK, check=True)
    print(f'Checks: {destination}', flush=True)
    return destination


def grow(args):
    selected = runtime(args.runtime)
    binary = selected / 'organism/organism'
    native_manifest = read(selected / 'organism/receipt.json')
    if hashlib.sha256(binary.read_bytes()).hexdigest() != native_manifest['images'][str(binary)]:
        raise RuntimeError('Native growth image binding failed. Run ./organism build.')
    out = Path(args.out).expanduser().resolve() if args.out else fresh('runs')
    out.mkdir(parents=True, exist_ok=False)
    command = [str(binary), str(args.steps), str(args.mask)]
    if not args.exact:
        command.append(str(selected / 'vgi_organism.so'))
    started = time.monotonic()
    with (out / 'stdout').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
        process = subprocess.Popen(command, cwd=WORK, stdout=stdout, stderr=stderr)
        ticks = Path(f'/proc/{process.pid}/stat').read_text().rsplit(')', 1)[1].split()[19]
        write(out / 'active.json', {'status': 'running_at_record', 'pid': process.pid,
                                   'process_start_ticks': ticks, 'command': command,
                                   'application': 'native-growth', 'requested_steps': args.steps,
                                   'source_mask': args.mask, 'vgi': not args.exact,
                                   'pid_namespace': os.readlink('/proc/self/ns/pid')})
        print(f'Native growth PID {process.pid}; run: {out}', file=sys.stderr if args.json else sys.stdout, flush=True)
        try:
            code = process.wait()
        except KeyboardInterrupt:
            process.terminate();code = process.wait()
    report = {'application': 'native-growth', 'command': command, 'source_mask': args.mask,
              'requested_steps': args.steps, 'vgi': not args.exact, 'exit_code': code,
              'process_seconds': time.monotonic() - started,
              'status': 'completed' if code == 0 else 'stopped' if code < 0 else 'failed'}
    if code == 0:
        value = read(out / 'stdout')
        assert value['source'] == args.mask and 0 <= value['continuation'] <= args.steps
        write(out / 'return.json', value)
        report.update(completed_steps=value['continuation'], actions=len(value['actions']), nodes=len(value['nodes']))
    write(out / 'receipt.json', report)
    write(out / 'active.json', {'status': 'terminal', 'receipt': str(out / 'receipt.json')})
    result={'run': str(out), **report}
    print(json.dumps(result,indent=2) if args.json else summary(result))
    return 0 if code == 0 else 3


def positive(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return number


def main(argv=None):
    parser = argparse.ArgumentParser(prog='organism', description=__doc__, epilog='Inc/P1/C re-entry, residue lifting, torus operations and VGI feedback execute inside factor. No separate producer is invoked.')
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('build', help='cleanly build and select the complete native organism');p.add_argument('--out', type=Path)
    p = sub.add_parser('factor', help='run the organism from N alone', formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument('N', nargs='?', help='odd decimal N, at least 128 bits');p.add_argument('--source', type=Path, help='N-only decimal file')
    p.add_argument('--runtime', type=Path, help='built runtime; otherwise use selected/latest runtime');p.add_argument('--out', type=Path, help='fresh output directory; otherwise timestamped')
    p.add_argument('--seconds', type=positive, default=600, help='native execution budget in seconds');p.add_argument('--workers', type=int, choices=range(1, 9), default=8, help='workers inside the shared witness computation')
    p.add_argument('--json', action='store_true')
    p = sub.add_parser('grow', help='run the native growing body, with VGI attached by default', formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument('--steps', type=int, default=12, help='growth steps; zero reads the initial body')
    p.add_argument('--mask', type=int, choices=range(16), default=8, help='native N,T,F,B membership mask')
    p.add_argument('--exact', action='store_true', help='execute native operations without the VGI learner')
    p.add_argument('--runtime', type=Path);p.add_argument('--out', type=Path);p.add_argument('--json',action='store_true')
    for name in ['status', 'inspect', 'stop', 'restart']:
        p = sub.add_parser(name, help={'status':'verify a run status and live PID', 'inspect':'read a receipt or native logical re-entry trace', 'stop':'stop the verified native process', 'restart':'stop, rebuild and restart the same N with a fresh timeout'}[name])
        p.add_argument('run', nargs='?', type=Path, help='run directory; defaults to latest')
        if name in ['status', 'inspect']:
            p.add_argument('--json', action='store_true')
        if name == 'inspect':
            detail=p.add_mutually_exclusive_group()
            detail.add_argument('--trace', action='store_true', help='show actual Inc/P1/C events')
            detail.add_argument('--stats', action='store_true', help='show retained native factor/phase statistics')
            detail.add_argument('--polynomials', action='store_true', help='show executed torus actions on root-sign polynomials')
            p.add_argument('--limit', type=positive, default=12)
        if name == 'restart':
            p.add_argument('--seconds', type=positive, default=600);p.add_argument('--workers', type=int, choices=range(1, 9), default=8)
            p.add_argument('--out', type=Path);p.add_argument('--json', action='store_true')
    p = sub.add_parser('check', help='check native organism and its arithmetic/re-entry components')
    p.add_argument('--component', choices=['all', 'native', 'continuation', 'cli', 'arithmetic', 'roots', 'phase', 'reentry'], default='all');p.add_argument('--out', type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == 'build':
            with exclusive():build(args.out)
        elif args.command == 'factor':
            if bool(args.N) == bool(args.source):parser.error('factor requires exactly one of N or --source')
            with exclusive():return factor(args)
        elif args.command == 'grow':
            if args.steps < 0:parser.error('--steps must be nonnegative')
            with exclusive():return grow(args)
        elif args.command == 'check':
            if args.component == 'cli':
                destination = Path(args.out).expanduser().resolve() if args.out else fresh('checks')
            else:
                with exclusive():destination = check(args.component, args.out)
            # The lifecycle check invokes real CLI commands, each owning its lock.
            if args.component in ['all', 'cli']:
                subprocess.run([sys.executable, str(KERNEL / 'organism/verify_cli.py'),
                                '--out', str(destination / 'cli')], cwd=WORK, check=True)
        elif args.command == 'stop':stop(run_path(args.run))
        elif args.command == 'restart':
            path = run_path(args.run);report = state(path)
            source = report.get('command', [None, None])[1]
            if not source:raise RuntimeError('The saved run has no source command.')
            stream=sys.stderr if args.json else None
            stop(path,stream=stream)
            with exclusive(wait=10):
                selected = build(stream=stream)
                if report.get('application')=='native-growth':
                    return grow(argparse.Namespace(runtime=selected,steps=report['requested_steps'],mask=report['source_mask'],
                                                   exact=not report['vgi'],out=args.out,json=args.json))
                return factor(args, selected=selected, source_override=source)
        else:
            path = run_path(args.run);report = state(path)
            if args.command == 'inspect' and args.polynomials:
                task = read(path / 'return.json').get('task')
                if task is None:raise RuntimeError('This growth run has no root-sign polynomials.')
                actions = task.get('square_polynomial_actions', [])[-args.limit:]
                if args.json:print(json.dumps(actions, indent=2))
                else:
                    print(summary(report))
                    for action in actions:
                        print(f"Family {action['family']}: B {action['before_b']} -> {action['after_b']}; changed={action['changed_b']}; inverse={action['inverse_verified']}")
                return 0
            if args.command == 'inspect' and args.stats:
                task = read(path / 'return.json').get('task')
                if task is None:raise RuntimeError('This growth run has no factor-phase statistics.')
                print(json.dumps(task['stats'], indent=2));return 0
            if args.command == 'inspect' and args.trace:
                task = read(path / 'return.json').get('task')
                if task is None:raise RuntimeError('For this growth run, read its return.json action history.')
                events = [e for op in task['operations'] for e in op.get('logical_reentry', [])] + task.get('pending_logical_reentry', [])
                if args.json:print(json.dumps(events[-args.limit:], indent=2))
                else:
                    print(summary(report))
                    for event in events[-args.limit:]:
                        membership = lambda value: '{' + ','.join(atom for i, atom in enumerate(['N','T','F','B']) if int(value['numeral']) & (1 << i)) + '}'
                        print(f"{event['operation']}: {membership(event['before'])} -> {membership(event['after'])}; TF={event['TF_shadow']}; designated={event['designated']}")
            else:print(json.dumps(report, indent=2) if args.json else summary(report))
        return 0
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f'organism: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())

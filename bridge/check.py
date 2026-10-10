"""Exercise both hosted frontends against Lean certificates and runtime maps."""
import ast
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def invoke(binary, args, code=0, env=None, data=None):
    result = subprocess.run([str(binary), *args], capture_output=True, text=True,
                            timeout=60, env=env, input=data)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result.stdout


for repo, name in [("Vox", "vox"), ("G-mOMonadOS", "g-momonados")]:
    binary = ROOT / repo / "target/release" / name
    for op, expected in {
        "join_i": lambda x: x | 5,
        "meet_i": lambda x: x & 5,
        "join_t": lambda x: ((x & 5) & 5) | ((x | 5) & 10),
        "meet_t": lambda x: ((x | 5) & 5) | ((x & 5) & 10),
        "join_f": lambda x: ((x & 5) & 3) | ((x | 5) & 12),
        "meet_f": lambda x: ((x | 5) & 3) | ((x & 5) & 12),
    }.items():
        report = invoke(binary, ["reentry", op, "5"])
        table = ast.literal_eval(next(line[6:] for line in report.splitlines() if line.startswith("table=")))
        assert table == [expected(i) for i in range(16)], (op, report)
        assert f"least={table[0]} greatest={table[15]} certified=true" in report
    report = invoke(binary, ["reentry", "orbit", "2", "1000000000001", "negation"])
    assert "period=2 tick=1000000000001 value=4 cycle-certified=true" in report
    report = invoke(binary, ["reentry", "program", "Y", "K", "K", "data:6", "@", "@", "@"])
    assert "kernel-reentry=6" in report
    assert "least=6 greatest=6 certified=true" in report
    for name, low, high in [("retain-after-inject", 2, 7), ("inject-after-retain", 10, 15)]:
        report = invoke(binary, ["reentry", name, "7", "10"])
        assert f"least={low} greatest={high} certified=true" in report
    report = invoke(binary, ["reentry", "word", "⊢∈≻⋈⊙⊤≻⋈⊥≺⋈⊞∋⊡⋈⊙⊣", "0", "1000000000000"])
    assert "least=15 native-fixed-point-checked=true" in report
    assert "greatest=15 native-greatest-fixed-point-checked=true" in report
    assert "tick=1000000000000 value=15 orbit-closure-checked=true" in report
    report = invoke(binary, ["reentry", "word", "⊙", "0", "1000000000000"])
    assert "fixed-point-certificate=unavailable" in report
    assert "tick=1000000000000 value=8 orbit-closure-checked=true" in report
    invoke(binary, ["reentry", "program", "K"], code=2)
    invoke(binary, ["reentry", "join_i", "16"], code=2)
    invoke(binary, ["reentry", "table", "0", "4", "1"], code=2)
    invoke(binary, ["reentry", "word", "⊡?"], code=2)
    invoke(binary, ["help"], code=2, env={**os.environ, "P4RAKERNEL_ROOT": "/tmp/nonexistent-kernel-bridge-check"})
    print(f"PASS {name}: native lattice tables, Y reduction, re-entry, feedback clocks, word maps and failed admission", flush=True)

report = invoke(ROOT / "Vox/target/release/vox", ["classify", "ret"])
assert "backend=" not in report  # Startup checks do not pollute payload output.
print("PASS existing Vox payload output remains clean", flush=True)

report = invoke(ROOT / "G-mOMonadOS/target/release/g-momonados", [], data=
                "reentry join_i 5\nvox reentry Y 6\np4ra reentry orbit 2 1000000000001 negation\nquit\n")
assert "least=5 greatest=15 certified=true" in report
assert "least=6 greatest=6 certified=true" in report
assert "period=2 tick=1000000000001 value=4 cycle-certified=true" in report
print("PASS G REPL, Vox and p4ra aliases release their Lean reports through the command vessel", flush=True)

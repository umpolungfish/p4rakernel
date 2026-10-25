#!/usr/bin/env python3
"""Build and execute the native kernel/VGI organism, preserving its full return."""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import time
import argparse
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, help='fresh output directory; defaults to a timestamped measurement directory')
options = parser.parse_args()
OUT = (options.out or ROOT / 'measurements/dialetheic_organism' /
       datetime.now(timezone.utc).strftime('verify_%Y%m%dT%H%M%S_%fZ')).resolve()
BOUND = WORK / "VGI/composed_source_joint_native_r2_20261017/runtime"
if OUT.exists():
    raise SystemExit(f'Output directory already exists; choose a fresh --out: {OUT}')
OUT.mkdir(parents=True)
records = []


def run(name, command, cwd=ROOT, stdout=None, env=None):
    start = time.monotonic()
    result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
    (OUT / (name + ".stdout")).write_bytes(result.stdout)
    (OUT / (name + ".stderr")).write_bytes(result.stderr)
    if stdout:
        (OUT / stdout).write_bytes(result.stdout)
    records.append(dict(name=name, command=[str(x) for x in command], cwd=str(cwd),
                        exit_code=result.returncode, seconds=time.monotonic() - start))
    (OUT / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
    print(name, result.returncode, flush=True)
    if result.returncode:
        raise RuntimeError((result.stdout + result.stderr).decode(errors="replace")[-4000:])
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


run("kernel_build", ["cmake", "--build", ROOT / "build/stage1", "--target", "leanshared", "-j2"])
run("lean_oracle", [ROOT / "build/stage1/bin/lean", "--run", "OrganismKernelOracle.lean"],
    cwd=ROOT / "p4ramill", stdout="lean_oracle.txt")
run("vgi_orders", ["cargo", "run", "--offline", "--release", "--features", "host", "--bin", "kernel_orders"],
    cwd=WORK / "VGI/sources/graph_flow_oracle", stdout="vgi_orders.txt")
oracle = [line.split() for line in (OUT / "lean_oracle.txt").read_text().splitlines() if line.startswith("lattice ")]
transport = [line.split() for line in (OUT / "vgi_orders.txt").read_text().splitlines()]
assert len(oracle) == len(transport) == 256
for left, right in zip(oracle, transport):
    assert left[1:3] == right[1:3]
    assert [left[i] for i in [3, 5, 6, 7, 8, 9, 10, 11]] == right[3:]

flags = ["c++", "-std=c++14", "-Wall", "-Wextra", "-Werror", "-I", ROOT / "src",
         "-I", ROOT / "build/stage1/include"]
run("native_build", flags + [ROOT / "tests/lean/run/organism_native.cpp", "-o", OUT / "organism_native"])
run("native_controls", [OUT / "organism_native", OUT / "lean_oracle.txt"])

bound = json.loads((BOUND / "build.json").read_text())
command = next(c.copy() for c in bound["commands"] if c[0] == "c++" and "-shared" in c)
command[command.index(str(BOUND / "full_model.cpp"))] = str(WORK / "VGI/sources/grammar_training_v1/organism_adapter.cpp")
command[command.index("-o") + 1] = str(OUT / "vgi_organism.so")
command += ["-I", str(BOUND)]
run("vgi_adapter_build", command)
run("vgi_native_build", flags + [ROOT / "tests/lean/run/organism_vgi_native.cpp", "-ldl", "-o", OUT / "organism_vgi_native"])
neural_control = json.loads(run("vgi_controls", [OUT / "organism_vgi_native", OUT / "vgi_organism.so"]))

run("lean_api", [ROOT / "build/stage1/bin/lean", "-o", OUT / "NativeDialetheicOrganism.olean",
                 "-c", OUT / "NativeDialetheicOrganism.c", "NativeDialetheicOrganism.lean"], cwd=ROOT / "p4ramill")
import os
environment = os.environ.copy()
environment["LEAN_PATH"] = str(OUT)
run("lean_entry", [ROOT / "build/stage1/bin/lean", "-c", OUT / "RunDialetheicOrganism.c", "RunDialetheicOrganism.lean"],
    cwd=ROOT / "p4ramill", env=environment)
run("native_entry_build", [ROOT / "build/stage1/bin/leanc", OUT / "NativeDialetheicOrganism.c",
                           OUT / "RunDialetheicOrganism.c", "-o", OUT / "organism"])
result = json.loads(run("native_entry", [OUT / "organism", "12", "8", OUT / "vgi_organism.so"], stdout="return.json"))
nodes, actions = result["nodes"], result["actions"]
assert result["source"] == 8 and result["continuation"] == 12
assert len(nodes) == len(actions) + 1
assert len(set(result["frontier"])) == len(result["frontier"])
assert len(result["judge_program"]) > 3
assert len(result["generator_program"]) > 2
assert sum(len(a["model_probes"]) for a in actions) > 0
assert any(a["judge_before"] != a["judge_after"] for a in actions)
assert all(len(a["judgment_trace"]) == len(a["judge_before"]) for a in actions)
assert all(n["boundary"] == 8 and n["source"] == 8 and n["articulation"] == [0, 1, 3, 7, 15] for n in nodes)
operations = 0
initial_optimizer_clock = result["actions"][0]["neural_operations"][0]["optimizer_before"]
for index, action in enumerate(actions):
    assert len(action["model_ancestry"]) == len(action["model_probes"])
    for ancestor in action["model_ancestry"]:
        assert ancestor < index
        assert actions[ancestor]["before"] == action["before"]
        assert actions[ancestor]["rule"] == action["rule"]
    assert nodes[index + 1]["parent"] == action["tip"]
    assert nodes[action["tip"]]["state"] == action["before"]
    assert nodes[index + 1]["state"] == action["after"]
    carried = action["before"]
    assert len(action["neural_operations"]) == len(action["program_before"])
    for neural in action["neural_operations"]:
        assert neural["input"] == carried
        assert neural["optimizer_before"] == initial_optimizer_clock + operations
        assert neural["optimizer_after"] == initial_optimizer_clock + operations + 1
        assert all(math.isfinite(x) for x in neural["rails_before"] + neural["rails_after"])
        carried = neural["proposal_after"]
        operations += 1
    assert carried == action["after"]
learner = result["learner"]
parameters = sum(p["size"] for p in bound["parameters"])
assert learner["optimizer_clock"] == initial_optimizer_clock + operations
assert all(len(learner[key]) == parameters for key in ["parameters", "adam_m", "adam_v"])
assert all(math.isfinite(x) for key in ["parameters", "adam_m", "adam_v"] for x in learner[key])
assert any(x != 0 for x in learner["adam_m"]) and any(x != 0 for x in learner["adam_v"])
assert all(len(channel) == bound["config"]["d_model"] for channel in learner["memory"])
clock = result["clock"]["cells"]
assert all(cell in [[1, 0], [0, 1]] for cell in clock)
assert sum(cell[0] << i for i, cell in enumerate(clock)) == operations

sources = [ROOT / p for p in ["src/kernel/inclosure.h", "src/kernel/inclosure.cpp", "src/kernel/organism_vgi.h", "src/kernel/organism_factor.h",
    "src/kernel/init_module.cpp", "src/kernel/CMakeLists.txt", "p4ramill/NativeDialetheicOrganism.lean",
    "p4ramill/RunDialetheicOrganism.lean", "p4ramill/OrganismKernelOracle.lean",
    "tests/lean/run/organism_native.cpp", "tests/lean/run/organism_vgi_native.cpp", "tests/kernel_features/verify_organism.py"]]
sources += [WORK / "VGI/sources/grammar_training_v1/organism_adapter.cpp",
            WORK / "VGI/sources/graph_flow_oracle/src/bin/kernel_orders.rs",
            BOUND / "full_model.cpp", BOUND / "build.json"]
report = dict(status="passed", register_transport_pairs=256, actions=len(actions), nodes=len(nodes),
              neural_operations=operations, parameter_count=parameters, source_mask=8,
              initial_optimizer_clock=initial_optimizer_clock,
              native_control=(OUT / "native_controls.stdout").read_text().splitlines()[-1],
              neural_control=neural_control, return_file=str(OUT / "return.json"),
              sources={str(p): digest(p) for p in sources},
              images={str(p): digest(p) for p in [OUT / "organism", OUT / "vgi_organism.so", ROOT / "build/stage1/lib/lean/libleanshared.so"]})
(OUT / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k not in ["sources", "images"]}), flush=True)

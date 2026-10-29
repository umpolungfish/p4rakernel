#!/usr/bin/env python3
"""Run the native and Lean kernel feature controls against the built stage1 toolchain."""
import json
import os
import re
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "measurements" / "kernel_features_20261009"
OUT.mkdir(parents=True, exist_ok=True)
ENV = os.environ.copy()
ENV["LEAN_PATH"] = str(ROOT / "build/stage1/lib/lean") + ":" + str(OUT)
LEAN = str(ROOT / "build/stage1/bin/lean")
RESULTS = []

def run(name, args):
    if sys.argv[1:] and name not in sys.argv[1:]:
        return
    completed = subprocess.run(args, cwd=ROOT, env=ENV, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = "\n".join(line.rstrip() for line in completed.stdout.splitlines())
    (OUT / (name + ".log")).write_text(output + ("\n" if output else ""))
    if "-c" in args and completed.returncode == 0:
        generated = Path(args[args.index("-c") + 1])
        generated.write_text("\n".join(line.rstrip() for line in generated.read_text().splitlines()) + "\n")
    diagnostics = [line for line in completed.stdout.splitlines()
        if re.search(r"\b(?:warning|error)(?:\([^)]*\))?:", line)]
    RESULTS.append({"name": name, "command": args, "exit_code": completed.returncode,
                    "diagnostics": diagnostics})
    (OUT / "results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
    print(f"{name}: exit {completed.returncode}", flush=True)
    if completed.returncode or diagnostics:
        print(completed.stdout, end="")
        sys.exit(completed.returncode or 1)

run("native_build", ["c++", "-std=c++17", "-Wall", "-Wextra", "-Werror", "-I", "src",
    "-I", "build/stage1/include", "tests/lean/run/sixteen3_native.cpp", "-o", str(OUT / "sixteen3_native")])
run("native_lattice_and_fixed_point", [str(OUT / "sixteen3_native")])
run("command_module_build", [LEAN, "--root=src", "-o",
    str(ROOT / "build/stage1/lib/lean/Init/Paraconsistent.olean"), "src/Init/Paraconsistent.lean"])
for name in ["sixteen3", "reentryValue", "reentry", "trilatticeMode", "kernel1", "kernel2", "interp", "interp2", "closure1", "nestedInductiveConstructions"]:
    run(name, [LEAN, "tests/lean/run/" + name + ".lean"])
run("module_export", [LEAN, "--root=tests/kernel_features", "-o", str(OUT / "ReentryExport.olean"),
    "-c", str(OUT / "export.c"), "tests/kernel_features/ReentryExport.lean"])
run("module_import", [LEAN, "--root=tests/kernel_features", "-c", str(OUT / "import.c"),
    "tests/kernel_features/ReentryImport.lean"])
run("interpreted_import", [LEAN, "--run", "tests/kernel_features/ReentryImport.lean"])
run("compiled_import_build", [str(ROOT / "build/stage1/bin/leanc"), str(OUT / "export.c"),
    str(OUT / "import.c"), "-o", str(OUT / "reentry_runtime")])
run("compiled_import", [str(OUT / "reentry_runtime")])
print("Selected kernel feature controls passed." if sys.argv[1:] else "All kernel feature controls passed.")

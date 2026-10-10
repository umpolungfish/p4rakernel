#!/usr/bin/env python3
"""Build the native NS extension with the fork and existing mathlib dependencies."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parent
OUT = ROOT / "measurements/ns_kernel_reentry_20261009"
OUT.mkdir(parents=True, exist_ok=True)
LEAN = ROOT / "build/stage1/bin/lean"
MATHLIB = PROJECT / ".lake/packages/mathlib"
HELPER = MATHLIB / "Mathlib/Lean/Expr/Basic.lean"

# The fork adds a ConstantInfo constructor. Preserve it in mathlib's two
# exhaustive conversions, keeping the dependency patch reproducible locally.
text = HELPER.read_text()
for anchor, addition in [
    ("  | recInfo    info, v => recInfo    {info with toConstantVal := v}",
     "  | reentryInfo info, v => reentryInfo {info with toConstantVal := v}"),
    ("  | opaqueInfo info => Declaration.opaqueDecl  info",
     "  | reentryInfo info => Declaration.reentryDecl info"),
]:
    if addition not in text:
        if anchor not in text:
            raise RuntimeError(f"Mathlib compatibility anchor missing: {anchor}")
        text = text.replace(anchor, anchor + "\n" + addition, 1)
if text != HELPER.read_text():
    HELPER.write_text(text)

paths = [str(p / ".lake/build/lib/lean")
         for p in sorted((PROJECT / ".lake/packages").iterdir())
         if (p / ".lake/build/lib/lean").is_dir()]
paths.append(str(PROJECT / ".lake/build/lib/lean"))
env = os.environ.copy()
env["LEAN_PATH"] = ":".join(paths)
results = []

def run(name, args, cwd=PROJECT):
    command = [str(LEAN), *map(str, args)]
    process = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
    output = process.stdout + process.stderr
    diagnostics = [line for line in output.splitlines()
                   if "warning:" in line or "error:" in line]
    (OUT / f"{name}.log").write_text(output)
    results.append({"name": name, "command": command, "cwd": str(cwd),
                    "exit_code": process.returncode, "diagnostics": diagnostics})
    (OUT / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"{name}: exit {process.returncode}", flush=True)
    if process.returncode or diagnostics:
        print(output, flush=True)
        raise SystemExit(process.returncode or 1)

run("command_module", ["--root=src", "-o",
    ROOT / "build/stage1/lib/lean/Init/Paraconsistent.olean",
    "src/Init/Paraconsistent.lean"], ROOT)
helper_output = MATHLIB / ".lake/build/lib/lean/Mathlib/Lean/Expr/Basic.olean"
run("mathlib_native_declarations", ["-o", helper_output,
    "Mathlib/Lean/Expr/Basic.lean"], MATHLIB)
for module in ["NS_Reentry", "NS_InjectionField", "NS_KernelReentry"]:
    target = PROJECT / f".lake/build/lib/lean/Imscribing/{module}.olean"
    target.parent.mkdir(parents=True, exist_ok=True)
    run(module, ["-o", target, f"Imscribing/{module}.lean"])
    (OUT / f"{module}.olean").write_bytes(target.read_bytes())
run("imported_controls", ["Imscribing/NS_KernelReentryAudit.lean"])
sources = [Path(__file__), HELPER, PROJECT / "Imscribing/NS_KernelReentry.lean",
           PROJECT / "Imscribing/NS_KernelReentryAudit.lean",
           PROJECT / "Imscribing/NS_Reentry.lean",
           PROJECT / "Imscribing/NS_InjectionField.lean", LEAN]
sources += list(OUT.glob("*.olean"))
(OUT / "verified_inputs.json").write_text(json.dumps({str(p):
    hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}, indent=2) + "\n")

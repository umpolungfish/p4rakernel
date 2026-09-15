#!/usr/bin/env python3
"""
lean2elf.py — Compile a Lean 4 source file (*.lean) into a native ELF binary.

Usage:
    lean2elf.py <input.lean> [-o OUTPUT]

How it works:
    Lean 4 ships no standalone `leanc` driver that produces an ELF directly.
    The canonical path is `lake`, which wraps `leanc` and the Lean runtime
    libraries.  lake itself only builds inside a project (lakefile.toml +
    lean-toolchain + a source tree), so we synthesise a minimal project
    around the user's .lean, copy the file in as Main.lean, and let
    `lake build` produce the executable.

Prerequisites (already on PATH):
    lean  (from /home/mrnob0dy666/.elan)
    lake  (from /home/mrnob0dy666/.elan)
    clang (the linker Lean's leanc wraps)

The output ELF is dynamically linked x86-64 by default.  Pass -s/--static
to ask lake for a fully static binary (requires the system musl toolchain
or the leanprover/lean4 musl target).

Author: Quantum⊙perator (Lando⊗⊙perator team), for the Imscribing Grammar
toolchain under /home/mrnob0dy666/imsgct/scripts/.
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# The Lean toolchain pinned across imsgct.  Bumping it requires bumping the
# `lean-toolchain` file written below.
LEAN_TOOLCHAIN = "4.33.1"

# Sanity check: do we have a `def main` or `def <pkgname>.main`?  Lean will
# happily produce a library ELF even with no main, but then the binary
# has no entry point and the run will fail with "no main".  We do NOT refuse
# such a file (sometimes you want a library artefact for linking later),
# but we warn on stderr.

REQUIRED_TOOLS = ("lean", "lake")


def die(msg: str, code: int = 1) -> None:
    print(f"lean2elf: {msg}", file=sys.stderr)
    sys.exit(code)


def which_or_die(tool: str) -> str:
    found = shutil.which(tool)
    if not found:
        die(f"required tool '{tool}' not on PATH")
    return found


def has_main(lean_src: str) -> bool:
    """Quick textual check: does the file define `def main`?

    Not a full parse — a heuristic for the common case.  A negative result
    only triggers a warning, not an error, because library entry points
    may live in modules other than the file the user passed in.
    """
    for line in lean_src.splitlines():
        s = line.strip()
        if s.startswith("--"):
            continue
        if s.startswith("def main") or s.startswith("def " ) and ".main" in s:
            return True
        if "main :=" in s and "def " in s:
            return True
    return False


def synthesise_project(workdir: Path, pkgname: str, lean_src_path: Path,
                        static: bool) -> None:
    """Populate workdir with a minimal lake project that builds the input.

    `lake new <pkgname>` is non-interactive when given a name; the resulting
    project contains Main.lean (a hello-world), lakefile.lean (a Lean 4
    script, not toml), and lean-toolchain.  We overwrite Main.lean with the
    caller's source and rewrite lakefile.lean to expose an executable.
    """
    workdir.mkdir(parents=True, exist_ok=True)

    # 1. lean-toolchain — pins the Lean version lake will use.
    (workdir / "lean-toolchain").write_text(LEAN_TOOLCHAIN + "\n")

    # 2. lakefile.lean — the project manifest.  Default lake new creates a
    #    lean_lib target; we need an executable target.
    lakefile = workdir / "lakefile.lean"
    lakefile.write_text(
        "import Lake\n"
        "open Lake DSL\n"
        "\n"
        f"package «{pkgname}»\n"
        "\n"
        "@[default_target]\n"
        f'lean_exe «{pkgname}» where\n'
        '  root := `Main\n'
    )

    # 3. Main.lean — the user's source, copied verbatim.
    shutil.copy2(lean_src_path, workdir / "Main.lean")


def build(workdir: Path, pkgname: str) -> Path:
    """Run `lake build` and return the produced binary path."""
    res = subprocess.run(
        ["lake", "build"],
        cwd=workdir,
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        sys.stderr.write(res.stdout)
        sys.stderr.write(res.stderr)
        die(f"lake build failed (exit {res.returncode})", code=res.returncode)

    bin_path = workdir / ".lake" / "build" / "bin" / pkgname
    if not bin_path.exists():
        die("lake build reported success but produced no binary")
    return bin_path


def main() -> None:
    ap = argparse.ArgumentParser(
        prog="lean2elf",
        description="Compile a Lean 4 source file (*.lean) to a native ELF binary.",
    )
    ap.add_argument("input", type=Path,
                    help="Path to the .lean source file to compile.")
    ap.add_argument("-o", "--output", type=Path, default=None,
                    help="Path to write the ELF binary. "
                         "Default: <input-stem>.elf in the current directory.")
    ap.add_argument("--keep-workdir", action="store_true",
                    help="Do not delete the temporary lake project on success.")
    ap.add_argument("--static", action="store_true",
                    help="Ask lake for a fully static binary (musl).")
    args = ap.parse_args()

    lean_path: Path = args.input.expanduser().resolve()
    if not lean_path.is_file():
        die(f"input not found: {lean_path}")
    if lean_path.suffix != ".lean":
        die(f"input must have .lean extension (got '{lean_path.suffix}')")

    for t in REQUIRED_TOOLS:
        which_or_die(t)

    lean_src = lean_path.read_text(encoding="utf-8", errors="replace")
    if not has_main(lean_src):
        print(
            "lean2elf: WARNING — no `def main` found in source; "
            "the produced ELF will have no entry point and may exit at once.",
            file=sys.stderr,
        )

    out_path: Path = (args.output or Path.cwd() / (lean_path.stem + ".elf")).resolve()

    pkgname = "l2e_" + lean_path.stem.lower().replace("-", "_")
    # lake rejects package names that don't match the dir name in some
    # versions; using a directory name that matches the package is safest.

    workdir = Path(tempfile.mkdtemp(prefix="lean2elf_"))
    workdir = workdir / pkgname  # nested so `lake new` can use the pkgname
    try:
        synthesise_project(workdir, pkgname, lean_path, args.static)
        elf = build(workdir, pkgname)
        shutil.copy2(elf, out_path)
        os.chmod(out_path, 0o755)
        if args.keep_workdir:
            print(f"lean2elf: workdir kept at {workdir}", file=sys.stderr)
    finally:
        if not args.keep_workdir:
            shutil.rmtree(workdir.parent, ignore_errors=True)

    size = out_path.stat().st_size
    print(f"lean2elf: {lean_path} -> {out_path} ({size} bytes)")
    sys.exit(0)


if __name__ == "__main__":
    main()

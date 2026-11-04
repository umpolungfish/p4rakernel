#!/usr/bin/env python3
"""Check build inputs without invoking Lake, compiling, or updating dependencies."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args])


def inputs(project):
    kernel = project.parent
    result = {}
    for filename in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        path = project / filename
        result[filename] = digest(path) if path.is_file() else None
    manifest = json.loads((project / "lake-manifest.json").read_text())
    packages_dir = project / manifest.get("packagesDir", ".lake/packages")
    for package in manifest["packages"]:
        name = package["name"]
        repo = project / package["dir"] if package["type"] == "path" else packages_dir / name
        prefix = f"dependency/{name}"
        result[f"{prefix}/revision"] = git(repo, "rev-parse", "HEAD").decode().strip()
        result[f"{prefix}/tracked_changes"] = hashlib.sha256(
            git(repo, "diff", "--binary", "HEAD", "--", ".", ":!.lake")
        ).hexdigest()
        for name_bytes in git(repo, "ls-files", "--others", "--exclude-standard", "-z").split(b"\0"):
            if not name_bytes:
                continue
            filename = name_bytes.decode()
            path = repo / filename
            if path.is_file() and not path.is_symlink():
                result[f"{prefix}/untracked/{filename}"] = digest(path)
        for filename in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            path = repo / filename
            result[f"{prefix}/{filename}"] = digest(path) if path.is_file() else None
    for filename in ("lean", "lake", "leanc"):
        path = kernel / "build/stage1/bin" / filename
        result[f"toolchain/bin/{filename}"] = digest(path)
    for path in sorted((kernel / "build/stage1/lib/lean").glob("*shared*.so")):
        result[f"toolchain/lib/{path.name}"] = digest(path)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("check", "record"))
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--snapshot", type=Path, help="required for recording a new baseline")
    args = parser.parse_args()
    project = args.project.resolve()
    baseline = args.baseline or project / "build-state.json"
    current = inputs(project)
    if args.action == "record":
        if not args.snapshot or not (args.snapshot / "COMPLETE.json").is_file():
            parser.error("record requires --snapshot pointing to a completed recovery snapshot")
        if baseline.exists():
            parser.error("baseline already exists; preserve it and use a new --baseline path")
        data = {"schema": 1, "snapshot": str(args.snapshot.resolve()), "inputs": current}
        with baseline.open("x") as stream:
            json.dump(data, stream, indent=2, sort_keys=True)
            stream.write("\n")
        print(f"Recorded build inputs: {baseline}")
        return 0
    if not baseline.is_file():
        print(f"STOP: missing baseline {baseline}. No build was started.")
        return 2
    saved = json.loads(baseline.read_text())
    expected = saved["inputs"]
    changed = [key for key in sorted(expected.keys() | current.keys()) if expected.get(key) != current.get(key)]
    if changed:
        print("STOP: build inputs differ from the saved successful configuration:")
        for key in changed:
            print(f"  {key}")
        print(f"Recovery snapshot: {saved['snapshot']}")
        print("No build was started. Review the changes before invoking Lake.")
        return 1
    print("Build configuration, dependency revisions/patches, and toolchain match the saved baseline.")
    print("This check did not invoke Lake and does not certify changed proof sources.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

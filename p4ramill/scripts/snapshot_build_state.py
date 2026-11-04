#!/usr/bin/env python3
"""Copy the project and native toolchain locally, verify every copied regular file."""

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--resume", action="store_true", help="resume an incomplete snapshot; never replace a completed snapshot")
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    kernel = project.parent
    destination = args.destination.resolve()
    workspace = kernel.parent
    if not destination.is_relative_to(workspace) or destination.is_relative_to(kernel):
        parser.error("destination must be inside imsgct and outside p4rakernel")
    if (destination / "COMPLETE.json").exists():
        parser.error("a completed snapshot is never overwritten")
    destination.mkdir(parents=True, exist_ok=args.resume)
    mappings = [(project, destination / "p4ramill"),
                (kernel / "build/stage1", destination / "stage1"),
                (kernel / "src", destination / "kernel_src")]
    for source, target in mappings:
        print(f"Copying {source.name}; source is unchanged", flush=True)
        target.mkdir(exist_ok=args.resume)
        subprocess.run(["cp", "-a", "--update", "--reflink=auto", str(source) + "/.", str(target)], check=True)
    print("Verifying independent file copies and internal links", flush=True)
    count = 0
    external = []
    with (destination / "files.sha256.jsonl").open("w" if args.resume else "x") as manifest:
        for source, target in mappings:
            for current, dirs, files in os.walk(source, followlinks=False):
                for name in dirs + files:
                    original = Path(current) / name
                    copied = target / original.relative_to(source)
                    if original.is_symlink():
                        link = os.readlink(original)
                        resolved = Path(os.path.normpath(str(original.parent / link)))
                        replacement = None
                        for old, new in mappings:
                            if resolved.is_relative_to(old):
                                replacement = new / resolved.relative_to(old)
                                break
                        if replacement is not None:
                            copied.unlink()
                            copied.symlink_to(os.path.relpath(replacement, copied.parent))
                        else:
                            external.append({"path": str(copied.relative_to(destination)), "target": link})
                    elif original.is_file():
                        before = original.stat()
                        sha = digest(original)
                        if original.stat().st_mtime_ns != before.st_mtime_ns or digest(copied) != sha:
                            raise RuntimeError(f"changed during copy or copy mismatch: {original}")
                        if (before.st_dev, before.st_ino) == (copied.stat().st_dev, copied.stat().st_ino):
                            raise RuntimeError(f"snapshot shares a writable inode: {original}")
                        manifest.write(json.dumps({"path": str(copied.relative_to(destination)), "sha256": sha}) + "\n")
                        count += 1
                        if count % 10000 == 0:
                            print(f"Verified {count} files", flush=True)
    # Configuration and proof sources are preserved with their actual local edits.
    with (destination / "kernel_source_changes.patch").open("wb") as stream:
        subprocess.run(["git", "-C", str(kernel), "diff", "--binary", "HEAD"], stdout=stream, check=True)
    subprocess.run(["git", "-C", str(kernel), "bundle", "create", str(destination / "kernel_history.bundle"), "--all"], check=True)
    receipt = {"schema": 1, "verified_regular_files": count, "external_symlinks": external,
               "build_evidence": "Lando reported plain lake build completed successfully immediately before this snapshot",
               "kernel_revision": subprocess.check_output(["git", "-C", str(kernel), "rev-parse", "HEAD"], text=True).strip()}
    (destination / "COMPLETE.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Verified recovery snapshot: {destination}", flush=True)
    if external:
        print(f"External links recorded separately: {len(external)}; inspect COMPLETE.json before relocating.", flush=True)


if __name__ == "__main__":
    main()

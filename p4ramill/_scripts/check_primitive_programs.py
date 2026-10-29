"""Elaborate each primitive sequentially, then run the Lean program exporter."""
import json
import os
import subprocess
import time
from pathlib import Path

MILL = Path(__file__).resolve().parents[1]
PROJECT = MILL.parent.parent
RECEIPTS = PROJECT / "measurements" / "lean_primitive_expansion_20261024"


def main():
    os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    records = []
    for source in sorted((MILL / "Imscribing/Primitives/Types").glob("PrimitiveType*.lean")):
        relative = source.relative_to(MILL)
        output = MILL / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        started = time.monotonic()
        result = subprocess.run(["lean", "-o", str(output), str(relative)], cwd=MILL,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (RECEIPTS / (source.stem + ".log")).write_text(result.stdout)
        records.append({"module": str(relative), "exit_code": result.returncode,
                        "seconds": time.monotonic() - started})
        (RECEIPTS / "lean_checks.json").write_text(json.dumps(records, indent=2))
        print(f"{source.stem}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout, flush=True)
            raise SystemExit(result.returncode)
    result = subprocess.run(["lean", "--run", "_scripts/export_primitive_programs.lean"], cwd=MILL,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (RECEIPTS / "export.stderr").write_text(result.stderr)
    (RECEIPTS / "checked_export.json").write_text(result.stdout)
    if result.returncode:
        print(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    exported = json.loads(result.stdout)
    assert len(exported["programs"]) == len(records)
    print(f"Lean exported {len(records)} primitive programs", flush=True)


if __name__ == "__main__":
    main()

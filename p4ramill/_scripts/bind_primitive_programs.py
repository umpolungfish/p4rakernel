"""Preserve executable positions omitted by the original primitive generator.

This one-time migration checks the original scaffold's stage and label records
against the current Lean source before retaining its opcode and action lists.
Existing Lean definitions and catalog entries are never regenerated or edited.
"""
import hashlib
import json
import re
from pathlib import Path
from gen_primitive_types import executable_declarations

MILL = Path(__file__).resolve().parents[1]
PROJECT = MILL.parent.parent
SEEDS = PROJECT / "MoDoT" / "ob3ects" / "primitives"
TYPES = MILL / "Imscribing" / "Primitives" / "Types"
RECEIPTS = PROJECT / "measurements" / "lean_primitive_expansion_20261024"
PATTERN = re.compile(r"(?:private )?def\s+(\w+_[sl]\d+)\s*:\s*Imscription\s*:=\s*(\{[^}]*\})")


def stages(text):
    return {name: re.sub(r"\s+", "", value) for name, value in PATTERN.findall(text)}


def main():
    records = []
    imports = []
    rows = []
    for source in sorted(TYPES.glob("PrimitiveType*.lean")):
        text = source.read_text()
        prefix = re.search(r"def (\w+)_family\s*:", text)[1]
        name = prefix.removeprefix("the_primitive_type_called_")
        original = SEEDS / f"the_primitive_type_called_{name}_ob3ect.json"
        data = json.loads(original.read_text())
        assert stages(text) and stages(text) == stages(data["lean_scaffold"]), name
        steps = data["phases"]["phase_4"]["steps"]
        expected = int(re.search(r"_bootstrapSteps\s*:\s*Nat\s*:=\s*(\d+)", text)[1])
        assert len(steps) == expected, name
        declarations = executable_declarations(prefix, steps, data["topology_report"]["pair_list"])
        if f"def {prefix}_opcodes :" not in text:
            text = text.replace("import Imscribing.IGFunctor\n", "import Imscribing.IGFunctor\nimport Imscribing.ConventionalRegister\n", 1)
            text = text.replace("end Imscribing.Primitives.Types", declarations + "\nend Imscribing.Primitives.Types", 1)
            source.write_text(text)
        imports.append("import Imscribing.Primitives.Types." + source.stem)
        rel = str(source.relative_to(MILL))
        rows.append(f'  ({json.dumps(name)}, {json.dumps(rel)}, {prefix}_glyphWord, {prefix}_opcodes, {prefix}_domainActions, {prefix}_forkFusePairs)')
        records.append({"name": name, "source": rel, "original_artifact": str(original.relative_to(PROJECT)),
                        "stage_and_label_records_match": True, "positions": expected,
                        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
    exporter = MILL / "_scripts" / "export_primitive_programs.lean"
    exporter.write_text("\n".join(imports) + '''
import Lean

open Imscribing Imscribing.Primitives.Types Lean

def primitiveProgramRows : List (String × String × String × List String × List String × List (Nat × Nat)) := [
''' + ",\n".join(rows) + '''
]

def main : IO Unit := do
  let programs := primitiveProgramRows.map fun (name, source, word, opcodes, actions, pairs) =>
    Json.mkObj [("name", toJson name), ("source", toJson source),
      ("word", toJson word), ("opcodes", toJson opcodes),
      ("actions", toJson actions), ("pairs", toJson pairs)]
  IO.println (Json.mkObj [("schema", toJson (1 : Nat)), ("programs", toJson programs)]).compress
''')
    RECEIPTS.mkdir(parents=True, exist_ok=True)
    (RECEIPTS / "migration.json").write_text(json.dumps(records, ensure_ascii=False, indent=2))
    print(f"Retained executable positions in {len(records)} Lean primitive modules")


if __name__ == "__main__":
    main()

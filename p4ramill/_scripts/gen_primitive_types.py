#!/usr/bin/env python3
"""
Generate Lean modules for all 49 primitive value types from /mnt/d/TYPES/ ob3ect JSONs.
Each JSON contains a lean_scaffold field with the full IGProtocol formalization.
"""
import json
import os
import re
from pathlib import Path

JSON_DIR = Path("/mnt/d/TYPES")
OUT_DIR = Path("/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing/Primitives/Types")
LAKEFILE = Path("/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/lakefile.toml")

PRIMITIVE_FAMILY = {
    "dead": "Dimensionality", "ash": "Dimensionality", "array": "Dimensionality", "if": "Dimensionality",
    "ado": "Relational", "tot": "Relational", "ear": "Relational", "ian": "Relational",
    "vow": "Grammar", "gag": "Grammar", "measure": "Grammar", "ooze": "Grammar",
    "fee": "Chirality", "kick": "Chirality", "sure": "Chirality", "wool": "Chirality",
    "awe": "Protection", "oak": "Protection", "ah": "Protection", "zoo": "Protection",
    "judge": "Topology", "eat": "Topology", "mime": "Topology", "oil": "Topology", "are": "Topology",
    "church": "Polarity", "or": "Polarity", "out": "Polarity", "peep": "Polarity", "yew": "Polarity",
    "woe": "Criticality", "monad": "Criticality", "roar": "Criticality", "err": "Criticality", "ha_ha": "Criticality",
    "yea": "KineticChar", "air": "KineticChar", "egg": "KineticChar", "on": "KineticChar", "loll": "KineticChar",
    "age": "Fidelity", "ice": "Fidelity", "nun": "Fidelity",
    "bib": "Granularity", "thigh": "Granularity", "so": "Granularity",
    "hung": "Stoichiometry", "they": "Stoichiometry", "up": "Stoichiometry",
}

FAMILY_ORDER = {
    "Dimensionality": {"dead": 0, "ash": 1, "array": 2, "if": 3},
    "Relational": {"ado": 0, "tot": 1, "ear": 2, "ian": 3},
    "Grammar": {"vow": 0, "gag": 1, "measure": 2, "ooze": 3},
    "Chirality": {"fee": 0, "kick": 1, "sure": 2, "wool": 3},
    "Protection": {"awe": 0, "oak": 1, "ah": 2, "zoo": 3},
    "Topology": {"judge": 0, "eat": 1, "mime": 2, "oil": 3, "are": 4},
    "Polarity": {"church": 0, "or": 1, "out": 2, "peep": 3, "yew": 4},
    "Criticality": {"woe": 0, "monad": 1, "roar": 2, "err": 3, "ha_ha": 4},
    "KineticChar": {"yea": 0, "air": 1, "egg": 2, "on": 3, "loll": 4},
    "Fidelity": {"age": 0, "ice": 1, "nun": 2},
    "Granularity": {"bib": 0, "thigh": 1, "so": 2},
    "Stoichiometry": {"hung": 0, "they": 1, "up": 2},
}


def safe_name(name):
    if name == "if":
        return "If"
    if name == "or":
        return "Or"
    if name == "ha_ha":
        return "HaHa"
    return name.capitalize()


def process_json(json_path):
    with open(json_path) as f:
        d = json.load(f)
    basename = json_path.stem.replace("the_primitive_type_called_", "").replace("_ob3ect", "")
    family = PRIMITIVE_FAMILY.get(basename, "Unknown")
    ordinal = FAMILY_ORDER.get(family, {}).get(basename, -1)
    p0 = d["phases"]["phase_0"]
    surface_tokens = p0.get("surface_tokens", [])
    boundary_condition = p0.get("boundary_condition", "")
    p1 = d["phases"]["phase_1"]
    opcodes = {}
    for k, v in p1.items():
        opcodes[k] = {"element": v.get("chosen_element", ""), "justification": v.get("justification", "")}
    p4 = d["phases"]["phase_4"]
    steps = p4.get("steps", [])
    p3 = d["phases"]["phase_3"]
    registers = {
        "void_desc": p3.get("void_description", ""),
        "true_desc": p3.get("true_description", ""),
        "false_desc": p3.get("false_description", ""),
        "both_desc": p3.get("both_description", ""),
    }
    scaffold = d.get("lean_scaffold", "")
    fingerprint = ""
    for line in scaffold.split("\n"):
        if "Fingerprint:" in line:
            fingerprint = line.strip().lstrip("-- ")
    return {
        "basename": basename,
        "safe_name": safe_name(basename),
        "family": family,
        "ordinal": ordinal,
        "surface_tokens": surface_tokens,
        "boundary_condition": boundary_condition,
        "opcodes": opcodes,
        "steps": steps,
        "registers": registers,
        "scaffold": scaffold,
        "fingerprint": fingerprint,
    }

def generate_module(data):
    """Generate a complete Lean module from the processed JSON data."""
    basename = data["basename"]
    safe = data["safe_name"]
    family = data["family"]
    ordinal = data["ordinal"]
    tokens = data["surface_tokens"]
    boundary = data["boundary_condition"]
    scaffold = data["scaffold"]
    reg = data["registers"]

    module_name = f"PrimitiveType{safe}"
    lean_name = f"the_primitive_type_called_{basename}"

    lines = []
    lines.append(f"/-")
    lines.append(f"  Imscribing.Primitives.Types.{module_name}")
    lines.append(f"")
    lines.append(f"  Formalization of the primitive value type '{basename}'")
    lines.append(f"  Family: {family} (ordinal {ordinal})")
    lines.append(f"  Surface tokens: {', '.join(tokens)}")
    lines.append(f"  Author: Lando⊗⊙perator")
    lines.append(f"-/")
    lines.append(f"")
    lines.append(f"import Imscribing.Primitives.Core")
    lines.append(f"import Imscribing.Primitives.Imscription")
    lines.append(f"import Imscribing.Primitives.TierCrossing")
    lines.append(f"import Imscribing.IGMorphism")
    lines.append(f"import Imscribing.IGFunctor")
    lines.append(f"")
    lines.append(f"namespace Imscribing.Primitives.Types")
    lines.append(f"open Primitives")
    lines.append(f"open Dimensionality Topology Relational Polarity Grammar")
    lines.append(f"     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality")
    lines.append(f"")

    # Surface tokens
    lines.append(f"/-- Surface tokens for '{basename}' -/")
    lines.append(f"def {lean_name}_surfaceTokens : List String := {json.dumps(tokens)}")
    lines.append(f"")
    lines.append(f"/-- Boundary condition for '{basename}' -/")
    lines.append(f"def {lean_name}_boundaryCondition : String := {json.dumps(boundary)}")
    lines.append(f"")

    # Belnap registers
    lines.append(f"/-- Belnap FOUR register descriptions -/")
    lines.append(f"def {lean_name}_registerVoid : String := {json.dumps(reg['void_desc'])}")
    lines.append(f"def {lean_name}_registerTrue : String := {json.dumps(reg['true_desc'])}")
    lines.append(f"def {lean_name}_registerFalse : String := {json.dumps(reg['false_desc'])}")
    lines.append(f"def {lean_name}_registerBoth : String := {json.dumps(reg['both_desc'])}")
    lines.append(f"")

    # Opcode mapping as comments
    lines.append(f"/-- Opcode domain-semantic mapping -/")
    for opname, opdata in sorted(data["opcodes"].items()):
        element = opdata["element"]
        justification = opdata["justification"]
        lines.append(f"-- {opname}: {element}")
        lines.append(f"--   {justification}")
    lines.append(f"")

    # Parse and embed scaffold sections
    scaffold_lines = scaffold.split("\n")
    stage_defs = []
    label_defs = []
    protocol_def = []
    eval_defs = []
    theorem_defs = []
    eval_section = []
    current_section = None

    for line in scaffold_lines:
        stripped = line.strip()
        if stripped.startswith("--") or stripped == "":
            continue
        if "import " in stripped:
            continue
        if stripped == "namespace Imscribing":
            continue
        if "open " in stripped and any(x in stripped for x in ["Dimensionality", "Primitives", "Frobenius"]):
            continue

        if "private def " in stripped and "_s" in stripped and "Imscription" in stripped:
            stage_defs.append(line)
            current_section = "stage"
        elif "private def " in stripped and "_l" in stripped and "Imscription" in stripped:
            label_defs.append(line)
            current_section = "label"
        elif "noncomputable def " in stripped and "_protocol" in stripped:
            protocol_def.append(line)
            current_section = "protocol"
        elif "noncomputable def " in stripped and ("_true_arm" in stripped or "_false_arm" in stripped):
            eval_defs.append(line)
            current_section = "eval"
        elif stripped.startswith("theorem ") and "frobenius" in stripped.lower():
            theorem_defs.append(line)
            current_section = "theorem"
        elif "#eval" in stripped:
            eval_section.append(line)
            current_section = "evalline"
        elif "def " in stripped and "tier" in stripped.lower():
            theorem_defs.append(line)
            current_section = "theorem"
        else:
            if current_section == "stage":
                stage_defs.append(line)
            elif current_section == "label":
                label_defs.append(line)
            elif current_section == "protocol":
                protocol_def.append(line)
            elif current_section == "eval":
                eval_defs.append(line)
            elif current_section == "theorem":
                theorem_defs.append(line)
            elif current_section == "evalline":
                eval_section.append(line)

    if stage_defs:
        lines.append("-- Stage Imscriptions (per-node cumulative)")
        for line in stage_defs:
            lines.append(line)
        lines.append("")

    if label_defs:
        lines.append("-- Label Imscriptions (per-node delta)")
        for line in label_defs:
            lines.append(line)
        lines.append("")

    if protocol_def:
        lines.append("-- Main IGProtocol term")
        for line in protocol_def:
            lines.append(line)
        lines.append("")

    if eval_defs:
        lines.append("-- Evaluation arm sub-defs")
        for line in eval_defs:
            lines.append(line)
        lines.append("")

    if theorem_defs:
        lines.append("-- Verification theorems")
        for line in theorem_defs:
            lines.append(line)
        lines.append("")

    if eval_section:
        for line in eval_section:
            lines.append(line)
        lines.append("")

    # Metadata
    lines.append(f"/-- '{basename}' belongs to the {family} family at ordinal {ordinal} -/")
    lines.append(f"def {lean_name}_family : String := {json.dumps(family)}")
    lines.append(f"def {lean_name}_ordinal : Nat := {ordinal}")
    lines.append(f"def {lean_name}_bootstrapSteps : Nat := {len(data['steps'])}")
    lines.append(f"")
    lines.append(f"end Imscribing.Primitives.Types")
    lines.append(f"")

    return "\n".join(lines)

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    generated_modules = []

    json_files = sorted(JSON_DIR.glob("the_primitive_type_called_*_ob3ect.json"))
    print(f"Found {len(json_files)} JSON files")

    for jf in json_files:
        basename = jf.stem.replace("the_primitive_type_called_", "").replace("_ob3ect", "")
        family = PRIMITIVE_FAMILY.get(basename)
        if family is None:
            print(f"  SKIP {basename}: not in PRIMITIVE_FAMILY mapping")
            continue

        data = process_json(jf)
        module_name = f"PrimitiveType{data['safe_name']}"
        generated_modules.append(module_name)
        content = generate_module(data)

        out_path = OUT_DIR / f"{module_name}.lean"
        with open(out_path, "w") as f:
            f.write(content)
        print(f"  WROTE {out_path} ({len(content)} chars)")

    print(f"\nGenerated {len(generated_modules)} modules")

    # Write lakefile entries
    glob_entries = [f'  "Imscribing.Primitives.Types.{m}"' for m in sorted(generated_modules)]
    with open(OUT_DIR / "_lakefile_entries.txt", "w") as f:
        for e in glob_entries:
            f.write(e + ",\n")

    print(f"\nLakefile entries written to {OUT_DIR / '_lakefile_entries.txt'}")
    print(f"Add these to lakefile.toml under [[lean_lib]] globs")


if __name__ == "__main__":
    main()

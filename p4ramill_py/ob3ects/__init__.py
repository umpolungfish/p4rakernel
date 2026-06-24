"""p4ramill_py ob3ects — self-verifying implementations for all 263+ vault ob3ects."""
import pathlib, importlib, sys

VAULT = pathlib.Path("/home/mrnob0dy666/imsgct/ob3ect/digital/.vault")

def load_ob3ect(name):
    """Load an ob3ect by name from the vault."""
    py_path = VAULT / name / f"{name}_ob3ect.py"
    if not py_path.exists():
        raise FileNotFoundError(f"No ob3ect.py found for {name}")
    spec = importlib.util.spec_from_file_location(name, py_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def list_ob3ects():
    """List all available ob3ects."""
    return sorted(d.name for d in VAULT.iterdir()
                  if d.is_dir() and not d.name.startswith('.')
                  and (d / f"{d.name}_ob3ect.py").exists())

def verify_all():
    """Verify all ob3ects."""
    results = {}
    for name in list_ob3ects():
        try:
            mod = load_ob3ect(name)
            cls_name = ''.join(p.capitalize() for p in name.replace('-','_').split('_'))
            cls = getattr(mod, cls_name + 'Ob3ect', None)
            if cls:
                results[name] = cls().verify()
            else:
                results[name] = False
        except Exception as e:
            results[name] = f"ERROR: {e}"
    return results

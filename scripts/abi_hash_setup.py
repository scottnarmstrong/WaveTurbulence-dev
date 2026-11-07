#!/usr/bin/env python3
"""ABI hash via a Lake setup file: the fallback when `lake env lean` exceeds vm.max_map_count.
The probe is a module file `module / import <M> / #print <export>`. Imports are resolved through the frozen
module's own Lake setup file, plus the module itself, with every project module's .olean.private added so that
proof bodies are visible, as in a non-module import."""
import hashlib, json, subprocess, sys, tempfile, os
from pathlib import Path
root = Path(sys.argv[1]).resolve(); path = sys.argv[2]; export = sys.argv[3]
mode = sys.argv[4] if len(sys.argv) > 4 else "abi"   # "abi" (sha256 of #print) or "axioms" (raw #print axioms)
module = ".".join(Path(path).with_suffix("").parts)
rel = Path(path).with_suffix("")
setup = json.loads((root / ".lake/build/ir" / rel).with_suffix(".setup.json").read_text())
lib = root / ".lake/build/lib/lean"
def arts(m):
    p = lib / Path(*m.split("."))
    data = [str(p.with_suffix(s)) for s in (".olean", ".olean.server", ".olean.private") if p.with_suffix(s).exists()]
    ir = [str(p.with_suffix(s)) for s in (".ir.sig", ".ir") if p.with_suffix(s).exists()]
    return [data, ir]
for m, v in setup["importArts"].items():
    if m.startswith("WaveTurbulence"):
        priv = str((lib / Path(*m.split("."))).with_suffix(".olean.private"))
        if Path(priv).exists() and priv not in v[0]:
            v[0].append(priv)
setup["importArts"][module] = arts(module)
setup["name"] = "AbiProbe"; setup["isModule"] = True
with tempfile.TemporaryDirectory() as tmp:
    probe = Path(tmp) / "AbiProbe.lean"
    cmd = "#print axioms" if mode == "axioms" else "#print"
    probe.write_text(f"module\n\nimport all {module}\n{cmd} {export}\n", encoding="utf-8")
    sj = Path(tmp) / "AbiProbe.setup.json"; sj.write_text(json.dumps(setup))
    env = dict(os.environ, ELAN_NO_OVERRIDE_NOTICE="1")
    run = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", "--setup", str(sj), str(probe)], cwd=root,
                         capture_output=True, env=env)
if run.returncode != 0 or run.stderr or b"error" in run.stdout:
    raise SystemExit(f"probe failed for {export}:\n{run.stdout.decode()}{run.stderr.decode()}")
sys.stdout.write(run.stdout.decode() if mode == "axioms" else hashlib.sha256(run.stdout).hexdigest() + "\n")

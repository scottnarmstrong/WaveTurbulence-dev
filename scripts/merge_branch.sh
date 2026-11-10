#!/usr/bin/env bash
# Maintainer helper: merge a development branch into main, rebuilding the root WaveTurbulence.lean import list as the union
# of all tracked modules under WaveTurbulence/Frozen/Defs, WaveTurbulence/Foundations and WaveTurbulence/Paper, plus the
# theorem anchors that manifest/frozen.json lists as SEALED (DRAFT_SORRY anchors and their providers stay quarantined and
# are never imported by the root). Stages the result; run scripts/land_check.sh before committing.
# Usage: scripts/merge_branch.sh <branch>
set -uo pipefail
br="$1"
git merge --no-ff --no-commit "$br" >/dev/null 2>&1
python3 -I - <<'PY'
import json,pathlib,subprocess
r=pathlib.Path("WaveTurbulence.lean"); t=r.read_text(); lines=t.split("\n")
keep=[l for l in lines if not (l.startswith("public import WaveTurbulence.") or l.startswith(("<<<<<<<","=======",">>>>>>>")))]
mods=set()
for d in ("WaveTurbulence/Frozen/Defs","WaveTurbulence/Foundations","WaveTurbulence/Paper"):
    for p in pathlib.Path(d).rglob("*.lean") if pathlib.Path(d).exists() else []:
        mods.add("public import "+str(p)[:-5].replace("/","."))
for a in json.loads(pathlib.Path("manifest/frozen.json").read_text(encoding="utf-8"))["anchors"]:
    if a["kind"]=="theorem" and a["state"]=="SEALED":
        mods.add("public import "+a["path"][:-5].replace("/","."))
i=max(j for j,l in enumerate(keep) if l.startswith("public import"))
r.write_text("\n".join(keep[:i+1]+sorted(mods)+keep[i+1:]))
PY
git add -A WaveTurbulence.lean WaveTurbulence
if git diff --cached --name-only --diff-filter=U | grep -q .; then echo "UNRESOLVED CONFLICTS:"; git diff --cached --name-only --diff-filter=U; exit 1; fi
echo "merged $br (staged; run scripts/land_check.sh, then commit)"

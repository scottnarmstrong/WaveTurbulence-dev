#!/usr/bin/env bash
# Orchestrator landing gate: duplicate-declaration scan, full root build, then the staged-tree guard.
# Exits non-zero (and prints why) if any step fails. Usage, from the repository root: scripts/land_check.sh
set -uo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
python3 -I - <<'PY' || exit 1
import re,glob,collections,sys
seen=collections.defaultdict(list)
for f in glob.glob("WaveTurbulence/**/*.lean",recursive=True) + glob.glob("WaveTurbulenceVineParam/**/*.lean",recursive=True):
    if "/Frozen/" in f or "/Provider/" in f: continue
    ns=[]
    for line in open(f,encoding="utf8"):
        m=re.match(r"\s*namespace\s+(\S+)",line)
        if m: ns.append(m.group(1)); continue
        m=re.match(r"\s*end\s+(\S+)",line)
        if m and ns and ns[-1]==m.group(1): ns.pop(); continue
        m=re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|protected\s+)*(?:def|theorem|lemma|abbrev|structure|instance)\s+([^\s:({\[]+)",line)
        if m: seen[".".join(ns+[m.group(1)])].append(f)
d={k:sorted(set(v)) for k,v in seen.items() if len(set(v))>1}
if d:
    print("DUPLICATE DECLARATIONS:"); [print(" ",k,v) for k,v in d.items()]; sys.exit(1)
print("duplicate scan: OK")
# sorry/admit scan outside Frozen/ (DRAFT_SORRY anchors live there): lake build only warns on sorry.
bad=[]
for f in glob.glob("WaveTurbulence/**/*.lean",recursive=True) + glob.glob("WaveTurbulenceVineParam/**/*.lean",recursive=True):
    if "/Frozen/" in f: continue
    t=open(f,encoding="utf8").read()
    t=re.sub(r"/-.*?-/","",t,flags=re.S)          # block comments and docstrings
    t=re.sub(r"--[^\n]*","",t)                     # line comments
    t=re.sub(r'"(?:[^"\\]|\\.)*"','""',t)          # string literals
    for i,l in enumerate(t.split("\n")):
        if re.search(r"\b(sorry|admit)\b",l): bad.append(f"{f}: {l.strip()[:80]}")
if bad:
    print("SORRY/ADMIT FOUND:"); [print(" ",b) for b in bad[:20]]; sys.exit(1)
print("sorry scan: OK")
PY
log=$(mktemp)
WT_PRIO=1 ELAN_NO_OVERRIDE_NOTICE=1 nice -n 10 lake build WaveTurbulence >"$log" 2>&1
status=$?
if [ $status -ne 0 ] || grep -q "^error" "$log"; then
  grep -E "^error|✖" "$log" | head -20; rm -f "$log"; echo "ROOT BUILD FAILED"; exit 1
fi
grep -E "Build completed" "$log"; rm -f "$log"
"$root/scripts/check_index.sh" || { echo "GUARD FAILED"; exit 1; }
echo "LAND CHECK OK"

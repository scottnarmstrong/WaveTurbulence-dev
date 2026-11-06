#!/usr/bin/env bash
# Orchestrator helper: merge a worker branch into main, rebuilding the bounded root/area public-import indexes as the union
# of all tracked modules under WaveTurbulence/Frozen/Defs, WaveTurbulence/Foundations and WaveTurbulence/Paper, plus the
# theorem anchors that manifest/frozen.json lists as SEALED (DRAFT_SORRY anchors and their providers stay quarantined and
# are never imported by the root). Stages the result; run scripts/land_check.sh before committing.
# Usage: scripts/merge_branch.sh <branch>
set -euo pipefail
br="$1"
git merge --no-ff --no-commit "$br" >/dev/null 2>&1
python3 -I "$PWD/scripts/update_root_imports.py"
git add -A -- WaveTurbulence.lean WaveTurbulence \
  WaveTurbulenceVineParam.lean WaveTurbulenceVineParam lakefile.lean
if git diff --cached --name-only --diff-filter=U | grep -q .; then echo "UNRESOLVED CONFLICTS:"; git diff --cached --name-only --diff-filter=U; exit 1; fi
echo "merged $br (staged; run scripts/land_check.sh, then commit)"

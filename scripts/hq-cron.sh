#!/bin/bash
# Cron (twice an hour): refresh the HQ README AUTO blocks and history, commit and push them.
# Takes the main-checkout lock shared with wt-tools/integrate.sh; skips if main has uncommitted tracked changes.
cd /home/scott/WaveTurbulence-dev || exit 1
exec 9>/home/scott/wt-tools/main.lock; flock -w 600 9 || exit 0
[ -z "$(git status --porcelain --untracked-files=no)" ] || exit 0
python3 -I scripts/update_readme.py >/dev/null 2>&1 || exit 1
git add README.md docs/campaign/history.csv
git diff --cached --quiet || { git commit -qm "HQ auto-update (progress meter)"; git push -q origin main; }

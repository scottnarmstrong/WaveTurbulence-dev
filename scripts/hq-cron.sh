#!/bin/bash
# Cron (twice an hour): refresh the HQ README AUTO blocks and histories from origin/main, then commit and push them.
# Runs in a dedicated worktree (/home/scott/WaveTurbulence-worktrees/hq), never in the main checkout, and takes its own
# lock (wt-tools/hq.lock), not main.lock: long landings no longer block it. Up to three attempts on a failed push.
set -u
R=/home/scott/WaveTurbulence-dev; W=/home/scott/WaveTurbulence-worktrees/hq
ts() { date -u +%FT%TZ; }
exec 8>/home/scott/wt-tools/hq.lock; flock -w 600 8 || { echo "$(ts) hq.lock busy, skipped"; exit 0; }
[ -d "$W" ] || git -C "$R" worktree add -q --detach "$W" origin/main || { echo "$(ts) cannot create $W"; exit 1; }
cd "$W" || exit 1
for i in 1 2 3; do
  git fetch -q origin || { echo "$(ts) fetch failed (attempt $i)"; sleep 30; continue; }
  git reset -q --hard origin/main || exit 1
  python3 -I scripts/update_readme.py >/dev/null 2>&1 || { echo "$(ts) update_readme.py failed"; exit 1; }
  git add README.md docs/campaign/history.csv docs/campaign/flower.json docs/campaign/flower-history.csv \
    docs/campaign/gammalow.json docs/campaign/gammalow-history.csv
  git diff --cached --quiet && { echo "$(ts) no change"; exit 0; }
  git commit -qm "HQ auto-update (progress meter)"
  if git push -q origin HEAD:main; then echo "$(ts) pushed $(git rev-parse --short HEAD)"; exit 0; fi
  echo "$(ts) push failed (attempt $i); retrying"; sleep 30
done
echo "$(ts) GIVING UP after 3 attempts"; exit 1

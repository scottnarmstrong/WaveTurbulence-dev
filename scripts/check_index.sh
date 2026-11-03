#!/usr/bin/env bash
# Run the frozen-anchor guard and the module check on exactly the staged tree (the git index),
# exported to a temporary directory. Agent worktrees under .claude/ and untracked files are
# therefore never scanned. Usage, from the repository root:  scripts/check_index.sh
set -euo pipefail
root=$(git rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
git -C "$root" checkout-index -a --prefix="$tmp/"
python3 -I "$root/scripts/check_frozen_anchors.py" --root "$tmp" --manifest "$tmp/manifest/frozen.json"
if [ -f "$root/scripts/check_lean_modules.py" ]; then
  (cd "$tmp" && python3 -I "$root/scripts/check_lean_modules.py")
fi

#!/usr/bin/env python3
"""Regenerate the AUTO blocks of README.md (the campaign HQ) from docs/campaign/progress.json,
docs/campaign/workers.json, the frozen-anchor manifest and the git repository. Run from anywhere:

    python3 -I scripts/update_readme.py            # rewrite README.md and append docs/campaign/history.csv

The orchestrator runs it at every landing (wt-tools/integrate.sh) and a cron job runs it twice an hour
(scripts/hq-cron.sh). `assessed` in progress.json is the time of the last review of the done fractions.

Weights: Lean work items are the blueprint packets (docs/blueprint/GRAPH.md §E) with their difficulty weights
(sums of node weights L=1, M=2, H=4, VH=8); each frozen theorem anchor adds 1, credited when SEALED; the non-Lean
phases carry the explicit weights recorded in progress.json.
"""
import datetime
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
PROGRESS = ROOT / "docs" / "campaign" / "progress.json"
WORKERS = ROOT / "docs" / "campaign" / "workers.json"
HISTORY = ROOT / "docs" / "campaign" / "history.csv"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True).stdout


def bar(frac, width=10):
    frac = max(0.0, min(1.0, frac))
    n = round(frac * width)
    return "█" * n + "░" * (width - n)


def lean_lines_main():
    total = files = 0
    for f in git("ls-files", "*.lean").split():
        if f == "lakefile.lean":
            continue
        try:
            total += sum(1 for _ in open(ROOT / f, encoding="utf8"))
            files += 1
        except OSError:
            pass
    return total, files


def lean_lines_branches():
    """Lean lines added on w/* branches but not yet on main (git diff main...branch)."""
    total = 0
    for b in git("for-each-ref", "--format=%(refname:short)", "refs/heads/w/").split():
        for line in git("diff", "--numstat", f"main...{b}", "--", "*.lean").splitlines():
            parts = line.split("\t")
            if len(parts) == 3 and parts[0].isdigit():
                total += int(parts[0])
    return total


def frozen_counts():
    sealed = total = defs = 0
    m = ROOT / "manifest" / "frozen.json"
    try:
        data = json.load(open(m, encoding="utf8"))
    except (OSError, json.JSONDecodeError):
        return 0, 0, 0
    for entry in data.get("anchors", []):
        if entry.get("kind") == "definition":
            defs += 1
            continue
        total += 1
        if entry.get("state") == "SEALED":
            sealed += 1
    return sealed, total, defs


def age(ts):
    if not ts:
        return "—"
    mins = int((datetime.datetime.now(datetime.timezone.utc).timestamp() - int(ts)) / 60)
    return f"{mins} min ago" if mins < 120 else f"{mins // 60} h ago"


def workers_block():
    try:
        workers = json.load(open(WORKERS, encoding="utf8"))
    except (OSError, json.JSONDecodeError):
        return "_no workers.json_"
    rows = ["| tmux | model / account | packet | branch: last commit | brief |", "|---|---|---|---|---|"]
    for w in workers:
        ts = git("log", "-1", "--format=%ct", w["branch"]).strip() if w.get("branch") else ""
        ahead = git("rev-list", "--count", f"main..{w['branch']}").strip() if w.get("branch") else ""
        br = f"`{w['branch']}`: {age(ts)}" + (f", {ahead} unlanded" if ahead not in ("", "0") else "")
        rows.append(f"| {w['tmux']} | {w['model']} / {w['account']} | {w['packet']} | {br} | [brief]({w['brief']}) |")
    return "\n".join(rows)


def main():
    prog = json.load(open(PROGRESS, encoding="utf8"))
    sealed, frozen_total, frozen_defs = frozen_counts()
    rows, item_rows = [], []
    tot_w = tot_d = lean_w = lean_d = 0.0
    for part in prog["parts"]:
        if part["kind"] == "phase":
            w, d, n = part["weight"], part["weight"] * part["done"], 1
        elif part["kind"] == "items":
            w = sum(i["weight"] for i in part["items"])
            d = sum(i["weight"] * i["done"] for i in part["items"])
            n = len(part["items"])
            lean_w += w
            lean_d += d
            for i in sorted(part["items"], key=lambda i: (-i["done"], i["id"])):
                mark = "✅" if i["done"] >= 1 else ("🟡" if i["done"] > 0 else "⬜")
                item_rows.append(f"| {i['id']} | {i['item']} | {i['weight']:g} | ≈{i['lines_est']:,} | "
                                 f"{mark} {round(100 * i['done'])} % | {i['note']} |")
        else:  # sealing
            w, d, n = frozen_total, sealed, frozen_total
            lean_w += w
            lean_d += d
        tot_w += w
        tot_d += d
        frac = d / w if w else 0.0
        rows.append(f"| {part['part']} | {n} | {w:g} | {d:.1f} | `{bar(frac)}` {round(100 * frac)} % |")
    pct = 100 * tot_d / tot_w
    lean_pct = 100 * lean_d / lean_w if lean_w else 0.0
    main_lines, main_files = lean_lines_main()
    branch_lines = lean_lines_branches()
    est_total = prog.get("lines_est_total", 0)
    now = datetime.datetime.now(datetime.timezone.utc)
    stamp = now.strftime("%Y-%m-%d %H:%M UTC")
    updated = (f"> **Last updated: {stamp}** · **estimated completion {pct:.1f} %** (Lean proofs {lean_pct:.1f} %) · "
               f"frozen theorems sealed: {sealed} / {frozen_total} (+ {frozen_defs} frozen definitions) · "
               f"**{main_lines:,} lines of Lean on main** ({main_files} files) + {branch_lines:,} unlanded on worker "
               f"branches · blueprint estimate ≈ {est_total:,} lines")
    progress = "\n".join([
        f"### Estimated completion: **{pct:.1f} %**",
        "",
        f"`{bar(pct / 100, 30)}` {pct:.1f} %",
        "",
        "| Part of the project | Items | Weight | Done | Completion |",
        "|---|---|---|---|---|",
        *rows,
        f"| **Total** | | {tot_w:g} | {tot_d:.1f} | **{pct:.1f} %** |",
        "",
        f"Lean lines: {main_lines:,} on main + {branch_lines:,} on branches, of ≈ {est_total:,} estimated by the "
        f"blueprint (`{bar((main_lines + branch_lines) / est_total if est_total else 0, 20)}` "
        f"{100 * (main_lines + branch_lines) / est_total:.1f} % of the estimate).",
        "",
        "<details><summary>All Lean work packets (blueprint §E) with weight and status</summary>",
        "",
        "| Packet | Name | Weight | Lines (est.) | Done | Note |",
        "|---|---|---|---|---|---|",
        *item_rows,
        "",
        "</details>",
        "",
        f"Done fractions last reviewed: **{prog['assessed']}**. Source: "
        "[`docs/campaign/progress.json`](docs/campaign/progress.json); history: "
        "[`docs/campaign/history.csv`](docs/campaign/history.csv).",
    ])
    text = README.read_text(encoding="utf8")
    for key, body in (("updated", updated), ("progress", progress), ("workers", workers_block())):
        text = re.sub(rf"(<!-- AUTO:{key} -->).*?(<!-- /AUTO:{key} -->)",
                      lambda m, body=body: m.group(1) + "\n" + body + "\n" + m.group(2), text, flags=re.S)
    README.write_text(text, encoding="utf8")
    new = not HISTORY.exists()
    with open(HISTORY, "a", encoding="utf8") as h:
        if new:
            h.write("utc,completion_pct,lean_pct,main_lines,branch_lines,sealed,frozen_theorems\n")
        h.write(f"{now.strftime('%Y-%m-%dT%H:%MZ')},{pct:.2f},{lean_pct:.2f},{main_lines},{branch_lines},"
                f"{sealed},{frozen_total}\n")
    print(f"README updated: {pct:.1f} % overall, {lean_pct:.1f} % Lean, {main_lines} + {branch_lines} lines, "
          f"{sealed}/{frozen_total} sealed")


if __name__ == "__main__":
    main()

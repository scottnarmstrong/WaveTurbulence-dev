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
# Flower estimate (flowerest1): the orchestrator's packet ledger lives beside the flower world; it is copied into
# docs/campaign/flower.json at every run. Its weight and completion replace packet X2's in the overall meter.
FLOWER_LEDGER = pathlib.Path("/home/scott/wt-scratch/flower-core/FLOWER-STATUS.json")
FLOWER_COPY = ROOT / "docs" / "campaign" / "flower.json"
FLOWER_HISTORY = ROOT / "docs" / "campaign" / "flower-history.csv"
FLOWER_WORLD = pathlib.Path("/home/scott/wt-scratch/flower-core/world/src/WaveTurbulence/Foundations/Flower")
FLOWER_ICON = {"done": "✅", "checkpoint": "🟠", "running": "🟡", "queued": "⬜"}


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


def flower_credit(pk):
    if pk["status"] == "done":
        return 1.0
    if pk["status"] == "checkpoint":
        return float(pk.get("done", 0.0))
    return 0.0


def flower_block():
    """Render the flower status bar. Returns (markdown, total weight, done fraction, counts) or None."""
    try:
        led = json.load(open(FLOWER_LEDGER, encoding="utf8"))
    except (OSError, json.JSONDecodeError):
        return None
    FLOWER_COPY.write_text(json.dumps(led, indent=1, ensure_ascii=False) + "\n", encoding="utf8")
    rows, prow = [], []
    tw = td = 0.0
    cnt = {"done": 0, "checkpoint": 0, "running": 0, "queued": 0}
    for g in led["groups"]:
        gw = sum(p["w"] for p in g["packets"])
        gd = sum(p["w"] * flower_credit(p) for p in g["packets"])
        tw += gw
        td += gd
        st = [p["status"] for p in g["packets"]]
        for p in g["packets"]:
            cnt[p["status"]] = cnt.get(p["status"], 0) + 1
            part = f" {round(100 * flower_credit(p))} %" if p["status"] == "checkpoint" else ""
            prow.append(f"| {g['name']} | {p['id']} | {p['w']:g} | {FLOWER_ICON.get(p['status'], '?')} "
                        f"{p['status']}{part} | {p.get('note', '')} |")
        frac = gd / gw if gw else 0.0
        rows.append(f"| {g['name']} | {len(st)} | {st.count('done')} | {st.count('running')} | "
                    f"`{bar(frac)}` {round(100 * frac)} % |")
    frac = td / tw if tw else 0.0
    wl = 0
    if FLOWER_WORLD.exists():
        for f in FLOWER_WORLD.rglob("*.lean"):
            try:
                wl += sum(1 for _ in open(f, encoding="utf8"))
            except OSError:
                pass
    n = sum(cnt.values())
    md = "\n".join([
        f"### Flower estimate (`flowerest1` = frozen `layergardenFlower_v3`): **{100 * frac:.1f} %**",
        "",
        f"`{bar(frac, 30)}` {100 * frac:.1f} % · {cnt['done']} of {n} packets done, {cnt['checkpoint']} partial, "
        f"{cnt['running']} running, {cnt['queued']} queued · ledger updated {led.get('updated', '?')}",
        "",
        f"- **Paper proof:** ✅ {led.get('paper', '')}",
        f"- **Lean:** {wl:,} lines in the flower world (sorry-free, pinned to main), plus main-side threading on "
        "worker branches. When the cores close, the world lands on main and the chain "
        "`layergardenFlower_v3 → fixedpoint_v2 → propansatz_v2 → main_v2` is sealed.",
        f"- **Next:** {led.get('next', '')}",
        "- **Open risks:** " + "; ".join(led.get("risks", [])),
        "",
        "| Workstream | Packets | Done | Running | Completion |",
        "|---|---|---|---|---|",
        *rows,
        f"| **Total** | {n} | {cnt['done']} | {cnt['running']} | **{100 * frac:.1f} %** |",
        "",
        "<details><summary>All flower packets</summary>",
        "",
        "| Workstream | Packet | Weight | Status | Note |",
        "|---|---|---|---|---|",
        *prow,
        "",
        "</details>",
        "",
        f"{led.get('convention', '')} Source: [`docs/campaign/flower.json`](docs/campaign/flower.json); history: "
        "[`docs/campaign/flower-history.csv`](docs/campaign/flower-history.csv).",
    ])
    return md, tw, frac, cnt, wl


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
    fl = flower_block()
    if fl is not None:
        for part in prog["parts"]:
            for i in part.get("items", []):
                if i["id"] == "X2":
                    i["weight"], i["done"] = fl[1], fl[2]
                    i["note"] = (f"FLOWEREST: weight and completion from the flower ledger ({fl[3]['done']} packets "
                                 f"done, {fl[3]['running']} running, {fl[3]['queued']} queued; see the flower bar)")
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
    blocks = [("updated", updated), ("progress", progress), ("workers", workers_block())]
    if fl is not None:
        blocks.append(("flower", fl[0]))
    for key, body in blocks:
        text = re.sub(rf"(<!-- AUTO:{key} -->).*?(<!-- /AUTO:{key} -->)",
                      lambda m, body=body: m.group(1) + "\n" + body + "\n" + m.group(2), text, flags=re.S)
    README.write_text(text, encoding="utf8")
    new = not HISTORY.exists()
    with open(HISTORY, "a", encoding="utf8") as h:
        if new:
            h.write("utc,completion_pct,lean_pct,main_lines,branch_lines,sealed,frozen_theorems\n")
        h.write(f"{now.strftime('%Y-%m-%dT%H:%MZ')},{pct:.2f},{lean_pct:.2f},{main_lines},{branch_lines},"
                f"{sealed},{frozen_total}\n")
    if fl is not None:
        newf = not FLOWER_HISTORY.exists()
        with open(FLOWER_HISTORY, "a", encoding="utf8") as h:
            if newf:
                h.write("utc,flower_pct,done,checkpoint,running,queued,world_lines\n")
            c = fl[3]
            h.write(f"{now.strftime('%Y-%m-%dT%H:%MZ')},{100 * fl[2]:.2f},{c['done']},{c['checkpoint']},{c['running']},"
                    f"{c['queued']},{fl[4]}\n")
    print(f"README updated: {pct:.1f} % overall, {lean_pct:.1f} % Lean, {main_lines} + {branch_lines} lines, "
          f"{sealed}/{frozen_total} sealed")


if __name__ == "__main__":
    main()

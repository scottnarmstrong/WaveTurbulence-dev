# Current orchestrator brief

Codex is the orchestrator under D13, succeeding Claude session 30b41343-3acb-4168-9826-e7d8c6659375.
Read AGENTS.md, PLAN.md, DECISIONS.md, FINDINGS.md, RULINGS.md and CODEX-HANDOFF.md before acting. The original
Wave A audit brief is preserved in BRIEF-2026-11-03-AUDIT.md; its initial worker restrictions are historical.

Continue until the full campaign goal is proved, keeping source interpretations, shared APIs, manifest and
landings under one editor. Terra-medium coding workers are the default; Sol-low is the fallback. Keep HQ README,
progress.json and workers.json current. Estimates, compiled conditional helpers and sealed source results are
different states. D9-D11 require sealing the gamma>1/2 chain before starting the enlarged gamma<=1/2 vine family.

Use source-faithful exact statements, no black boxes and no hard conclusions as hypotheses. Frozen declarations
remain immutable except the registered sealing procedure or an independently audited versioned successor under
the standing authorization. A wrong or overbroad draft cannot be silently weakened and counted proved.

Workers own only their exact packet files. Main edits/merges take /home/scott/wt-tools/main.lock and run the
landing gate. Generate bounded public root indexes with scripts/update_root_imports.py; never restore a flat
root exceeding1500 lines. Stage explicit paths, inspect complete staged changes and preserve unrelated work.
Production code consumes registered implementations through SEALED anchors; ordinary proved Foundations modules
are not draft providers merely because a packet calls their exports providers.

New code source/input ports need exact consumer, axiom, module/quarantine and independent fidelity review. Scratch
olean coexistence is insufficient: validate source identities and rebuild in one canonical world before closure.
Source/author rulings R54-R58 and the R57 CanonicalObject watch in CODEX-HANDOFF remain active. Do not kill or
replace existing catalogue drivers or edit other sessions' owned artifacts.

Hard rules (verbatim):

1. **Never use `set_option maxHeartbeats`** or any other heartbeat, recursion-depth or synthesis-budget override.
   A default-budget failure is a design signal: refactor or split.
2. **No Lean file may exceed 1500 lines.** Split into focused modules before that point.
3. **Every `.lean` file is a Lean module.** File shape: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold, and every
   source-facing or frozen definition.
4. **No `axiom`, `admit`, `unsafe` or `opaque`.** `sorry` is allowed only as the manifest-bound body of an
   owner-approved frozen statement (`DRAFT_SORRY`). Placeholder definitions are forbidden.
5. **Frozen files are read-only.** If a frozen declaration looks wrong, stop and report. Never add a premise and never
   substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing data
   and explicit owner rulings. A conditional helper gets a distinct name and never stands in for a source result.
7. **Providers are quarantined.** Only the frozen anchor may import a provider or a `DRAFT_SORRY` anchor.
8. **Builds.** One targeted `nice -n 5 lake build <Module>` (or `lake env lean <file>`) at a time, through the
   `wt-throttled` compile gate. Never build the whole library, never `lake clean`, never rebuild Mathlib. A wait on
   the gate is expected, not a hang. This is a shared machine.
9. **Errata.** Report every suspected defect in the pinned sources in your handoff (location, quoted text, why it is
   wrong), and every deviation you introduce.

Handoff: files; approach; exact checks/results; axioms; uncertainties; errata/deviations. End READY <packet> or STOPPED <packet>: exact reason.

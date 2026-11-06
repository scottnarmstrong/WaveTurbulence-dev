User Scott asks to finish the WaveTurbulence campaign using Terra-medium code agents, Sol-low fallback. You are a Terra-medium worker. Read current main AGENTS.md, docs/campaign/PLAN.md, docs/DECISIONS.md, docs/FINDINGS.md and docs/campaign/orch/RULINGS.md, plus lean-workflow, lean-search-discovery, lean-proof-patterns and lean-learnings skills as applicable. The old orch/BRIEF.md is historical. Main and frozen files are read-only; no root-import edits, staging, commits, landings or upstream rebuilds. No subagents. Use existing inspected scratch wrappers and wt-throttled gate, one targeted niced compile at a time. Preserve all existing source originals/artifacts and other packets; report exact type/source/interface gaps rather than adding hypotheses. Native agents use disjoint files; existing external scratch sessions may still be present, so only new uniquely named files below are owned. No other sessions may be messaged or killed. Final-source certification requires later canonical-world build, exact consumer and axiom tests, and independent source review. Your local compilation does not promote a frozen theorem or close the campaign.

Goal: Resume LOW-FRONT at A4, after your A1-A3 milestone: adapt the actual counting collection/structural/Unsel data to M.unloop, using assembly-local C2Can and the new UnselOK branch (R50). Do not start the large LOW-CHAIN port. Scratch /home/scott/wt-scratch/finalcount-asm; previous handoff /home/scott/wt-scratch/codex-takeover/finalcount-low/HANDOFF-CODEX.md plus asm HANDOFF session19 and g3-lowdeg/src/GL26, GL27, related unloop modules.
Ownership: only NEW /home/scott/wt-scratch/finalcount-asm/src/AsmLowFront6*.lean, AsmLowFront7*.lean, AsmLowUnloop*.lean, plus NEW CODEX-LOWFRONT-A4* build/check scripts and /home/scott/wt-scratch/codex-takeover/finalcount-a4/**. AsmLowFront1-5, existing Asm/G3/Subpro source files and source originals/build dirs are read-only. Root will integrate exports. Keep the actual `C2Can` and UnselOK definitions fixed; if a transfer does not hold, derive a stronger producer from source geometry or report the exact obstruction.
Use existing proven hdet/heq, GL17 and LoopCtx application evidence. Target actual CollData/SubproOblG/UnselOK transfers and exact consumer examples on M.unloop, not an abstract helper with the desired transferred property as premise. Preserve source first/second collection classification, SG/LG/zero-gap conventions, fixed labels and root-base dependence. Canonical-world status remains provisional (farm8/build11 + g3-lowdeg/build-fresh1); record all interface hashes and do not claim FinalCountLowAt. Send an early exact interface/status and persist through the bounded transfer milestone; stop only for a precise mathematical or API obstruction.

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

Handoff: files; approach; exact checks and output; #print axioms; uncertainties; errata/deviations; evidence of consuming actual producer. End READY <packet> or STOPPED <packet>: exact reason.

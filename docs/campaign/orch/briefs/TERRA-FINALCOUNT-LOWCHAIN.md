User Scott asks to finish the WaveTurbulence campaign using Terra-medium code agents, Sol-low fallback. You are a Terra-medium worker. Read current main AGENTS.md, docs/campaign/PLAN.md, docs/DECISIONS.md, docs/FINDINGS.md and docs/campaign/orch/RULINGS.md, plus lean-workflow, lean-search-discovery, lean-proof-patterns and lean-learnings skills as applicable. The old orch/BRIEF.md is historical. Main and frozen files are read-only; no root-import edits, staging, commits, landings or upstream rebuilds. No subagents. Use existing inspected scratch wrappers and wt-throttled gate, one targeted niced compile at a time. Preserve all existing source originals/artifacts and other packets; report exact type/source/interface gaps rather than adding hypotheses. Native agents use disjoint files; existing external scratch sessions may still be present, so only new uniquely named files below are owned. No other sessions may be messaged or killed. Final-source certification requires later canonical-world build, exact consumer and axiom tests, and independent source review. Your local compilation does not promote a frozen theorem or close the campaign.

Goal: Continue LOW-CHAIN after the A4 handoff, with a bounded first milestone: derive the actual SubHypL class-counting bridge and degree-two run-index potential arithmetic. This is infrastructure below the still-open FinalCountLowAt source gate, not a replacement gate. Use session19 HANDOFF.md and AsmTopClass3.reg_class_bound as the eventual interface; retain Cstar before the polylog exponent m. Frozen target and main are read-only.

Ownership: only NEW /home/scott/wt-scratch/finalcount-asm/src/AsmLowChainCodex*.lean, NEW CODEX-LOWCHAIN* build/check scripts, and /home/scott/wt-scratch/codex-takeover/finalcount-lowchain/**. Previous A1-A4 modules, every existing REG/G3/Subpro/GL/GV source and every existing build directory remain read-only. Extend only your own new outputs. Do not spawn agents or stage/commit. Do not import both broad conflicting old G3 declaration closures; narrow the imports and record the exact provisional world.

First deliverable:
1. Prove the degree-deficit/card_lowdeg_le and finite class-label counting statements from actual SubHypL (no degree>=3 premise). Reuse source formulas of AsmClass/AsmClass2 and the common labelSet carrier; do not assume the desired cardinality bound. Preserve base/root/mate/decorations and fixed tame-label requirements.
2. Make the running index explicit in the potential consumed by the low run. Read GL1-GL6, GL14-GL16 and AsmPotW/AsmInputs. The state index drops on D3 and D1. GL14 explicitly proves deviation=1 for D3 with unchanged molecule and labels, and warns that the true-increment excessRHS is false. Prove exact changes in the actual potR factors and discharge D3 contraction using the index drop (and derived source-smallness conditions). Do not import a true-increment bound as a premise. For D1, state/prove the exact R-drop and dartless restrictions needed for the analogous assembly; report any missing rho/critical bridge rather than postulate it.
3. Use actual UStepD3/HStepD3 and where available UStepD1, not arbitrary relations carrying the desired conclusion. A literal internal potential definition is allowed, but it must describe this genuine source arithmetic, with no zero/default fallback. Keep source-level target propositions unchanged.

After the first milestone, checkpoint before expanding the chain. Provide the exact minimal LOW Hmem/Hend interface changes needed for AsmTopClass3, including coverage of HStepD1 and the R'=0 terminal case. Conditional internal cover lemmas must be named as conditional and never reported as FinalCountLowAt or a closed source node. No large mechanical port without first resolving the varying-index potential. The later LOW terminal split is LowFree -> Prop96, other low/tame components -> Prop96Damaged; garden producer remains separately open.

Validation: one targeted niced gated compile at a time, fresh own-module rebuild, exact consumer probes, #print axioms, source/input hashes, lint/line/module checks. Current farm8/build11 + g3-lowdeg/build-fresh1 is PROVISIONAL; canonical-world and independent review remain mandatory. No upstream or Mathlib rebuild. Report suspected source errata with exact location, quote and rationale; distinguish inherited deviations from new ones.

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

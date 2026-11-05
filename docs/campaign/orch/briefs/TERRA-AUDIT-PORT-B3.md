Goal: Independent refute-first READ-ONLY audit of the Batch-3 six-provider port in /home/scott/WaveTurbulence-worktrees/port-b3a (root is the author; you did not author this packet). Ownership: only /home/scott/wt-scratch/codex-takeover/audit-port-b3/** for report/probes. No other source edits, no git commits/landings, no model changes, no subagents. Root is compiling in the worktree; coordinate before any compile and do not run a concurrent build there. You may inspect static sources and existing logs while root builds.

Read current main AGENTS/PLAN/DECISIONS/FINDINGS and lean-statement-audit + lean-workflow skills. Recovered campaign source rulings are docs/campaign/orch/RULINGS.md (R33, R54-R58); port is separate from the unfinished V5/Stage1/finalcount work.

Evidence: /home/scott/wt-scratch/port-b3a/prepare.py and prepare-six.py, plan-six.json (source paths/hashes/import mapping), snapshot/**, DEDUP-IDENTITY.json; /home/scott/wt-scratch/provider-repin/HANDOFF.md, PIN.json, PROVIDER-TEXT-CHECK.json, FINAL-SHA256SUMS and per-provider checks. Source scratch aliases were pinned to lg-spine-u/build-fresh-a7. The root ports these to actual main Frozen defs and already landed theorem dependencies, not scratch oleans. Source comparison must account for existing main import mapping from port-b2a/b2b and plan-L5.

Targets (WaveTurbulence prefix): PL2330.coherentApproximationGate30 and leafwiseCoherentApproximationGate30; RA1Leafwise.leafwiseRegularAsymptotics; IncohLeafwise.leafwiseIncoherentDecay; ladder Fourier provider in Final4c; LadderDecay ladderDecayGate; coarse provider in GatePinned. Check exact fully-qualified names on disk. The old conditional hA : RegularAsymptoticsGate is acceptable only when it is discharged with actual sealed WaveTurbulence.regularAsymptotics in the planned combined test. Remaining named input gates may not be counted as closed.

Refute: duplicated declarations, frozen/placeholder/quarantine leaks, mismatched source carriers due import rewrites, changed provider hypotheses/results/quantifier scopes, silent copying of conclusion-shaped conditions, or new warnings. Compare all ported text against snapshot modulo imports/whitespace, inspect every real proof/signature repair. Root is cleaning pre-existing copied linter warnings by equivalent tactic substitutions; dropping an unused hd binder from one internal helper requires checking its one consumer, and does not authorize changing provider statements. No source-facing/frozen definition body may change.

A fresh main-package targeted build and exact consumer/axiom probes are required before READY; root will provide logs after compile. You may report static findings first. Do not certify based only on scratch READY or artifact coexistence. Write REPORT.md with PASS/FAIL/PENDING per source identity, binder, consumption, axiom, build, module/quarantine checks; all unresolved findings exact path:line and reason. Separate candidates needing mathematical source re-audit from mechanical port issues. No seal is being prepared, so no frozen theorem may be marked newly PROVED.

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

Handoff: files; approach; exact checks/output; axioms; uncertainties; suspected errata/deviations. End READY audit-port-b3 or STOPPED audit-port-b3: exact reason.

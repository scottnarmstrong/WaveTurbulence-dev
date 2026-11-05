Goal: Finish hygiene of the main-package Batch-3 six-provider port. Root owns source/import repairs; you own linter-proof repairs in the listed files. First finish and pin your existing V5 modulated-Step3 milestone and HANDOFF-CODEX; do not erase that work. Then switch to this packet. Root is assigning the switch explicitly; you need not continue unbounded V5 work at the same time.

Worktree /home/scott/WaveTurbulence-worktrees/port-b3a. Ownership: files under WaveTurbulence/Foundations/Spine EXCEPT WaveBDraft/Flower.lean, CoordinateDerivativeBound.lean, XNormPointwise.lean, SplicedAmplitudeSupport.lean, RA1LW/LeafSingularOutput.lean, SourceProviders.lean, GatePinned.lean. Root alone edits those seven excluded files. You may change ordinary proof scripts, pattern-binder names, and remove redundant expose annotations when enclosing @[expose] public section already exposes the definitions. Do not change any meaning-carrying definition bodies, exported provider hypotheses/types, or frozen files. No linter disables, budget overrides, placeholders or root import edits. No git commit/staging/landing; root owns index. Your report/probes go under /home/scott/wt-scratch/codex-takeover/lint-port-b3/.

Inspect /home/scott/wt-scratch/port-b3a/build-providers-1.log (finished failed build, about 299 warnings in copied modules). Fix every owned new-code warning. Most are deprecated aliases, unused tactics/simp arguments, unused pattern binders, and automatic section-instance inclusion. Preserve provider result signatures. For intentionally retained typing/standing inputs, naming existing anonymous section instances and explicitly `include`ing those same existing arguments may preserve the ABI without introducing a new hypothesis; prove with exact application tests. For vestigial helper premises, omit only when safe and adjust consumers within scope; coordinate cross-scope caller changes with root. Never use includes to add proof obligations or strengthen any statement.

Builds: no build is active when root sends your switch. Coordinate before compiling: root needs a targeted rebuild of SourceProviders after five import/name fixes. You may edit owned files while root edits disjoint excluded files, but do not launch a build until root grants the compile baton. Then run one targeted `nice -n 5 lake build WaveTurbulence.Foundations.Spine.SourceProviders` at a time through existing wt-throttled gate. Root and independent reviewer finalcount_low will review all nontrivial changes. Use exact source/diff evidence, not suppressions. Send early list of intended approach and keep root informed at checkpoints. Persist until no owned warnings/errors remain or a concrete mathematical obstacle requires root action.

Read AGENTS/PLAN/DECISIONS/FINDINGS and lean-workflow, lean-proof-patterns, lean-naming-style skills. Main/frozen/source originals and snapshots are read-only. Root may be changing seven excluded files concurrently; do not overwrite them or rerun prepare-six.py.

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

Handoff: exact changed files; proof/API effects; exact build commands/output; warning count by new area; axioms where affected; uncertainties/deviations. End READY lint-port-b3 or STOPPED lint-port-b3: exact reason.

# Common brief header (every prover reads this first)

Repo rules: `/home/scott/WaveTurbulence-dev/AGENTS.md` — read it fully; its **Hard rules** apply verbatim:

1. Never use `set_option maxHeartbeats` or any other heartbeat, recursion-depth or synthesis-budget override.
2. No Lean file may exceed 1500 lines.
3. Every `.lean` file is a Lean module (copyright, `module`, imports with `public import` for the interface, module
   docstring, `public section`; `@[expose]` on definitions whose bodies must unfold).
4. No `axiom`, `admit`, `unsafe` or `opaque`; no `sorry` anywhere in your files; no placeholder definitions.
5. Frozen files are read-only (none exist yet).
6. No conclusion-shaped hypotheses: theorems assume only source premises and typing data; a conditional helper gets a
   distinct name.
7. Providers are quarantined (none exist yet).
8. One targeted `nice -n 5 lake build WaveTurbulence.<Module>` or `nice -n 5 lake env lean <file>` at a time (the
   `wt-throttled` gate queues you; a wait is expected). Never build the whole library, never `lake clean`, never
   rebuild Mathlib.
9. Report suspected source errata and any deviation you introduce.

Working practice:
- Work only in your worktree (given in your brief) on your branch `w/<name>`; scratch files in
  `/home/scott/wt-scratch/<name>/`. Commit sorry-free, compiling modules on your branch at every milestone (several
  times per hour); do not push; the orchestrator lands your branch. Run `git merge main` when told a landing happened.
- Do not edit `WaveTurbulence.lean` (the root), other workers' files, or anything outside your worktree.
- Mathlib first (search `.lake/packages/mathlib`), then Scott's repos (clone into your scratch dir with
  `gh repo clone scottnarmstrong/<repo> /home/scott/wt-scratch/<name>/<repo> -- --depth 1`), then build.
- **Update 2026-11-03 (D6): Wave A is frozen.** The source-facing definitions now live in
  `WaveTurbulence/Frozen/Defs/` (one per file, read-only, namespace `WaveTurbulence`): `Mom`, `latticePoint`,
  `collisionOp`, `IsWKESolution`, `partialDeriv`, `normLaplacian`, `torusFourierCoeff`, `IsSmoothNLSSolution`,
  `stdComplexGaussian`, `initialCoeff`, `solvableEvent`, `kineticTime`, `weightedL2Norm`. Import them
  (`public import WaveTurbulence.Frozen.Defs.<File>`) and never redefine them. The theorems `WaveTurbulence.main`
  and `WaveTurbulence.wkelwp` are `DRAFT_SORRY` anchors: never import `WaveTurbulence.Frozen.Theorems.*` or
  `WaveTurbulence.Provider.*`.
- Definitions marked DRAFT below are the orchestrator's exact current drafts of source-facing definitions, pending
  author approval: copy them verbatim into the file named; if the approved version differs, the orchestrator will tell
  you and you adapt. Never change a DRAFT body yourself; if one looks wrong, say so in your handoff.
- Namespaces: new declarations go in `WaveTurbulence.<Area>` (your packet area) or are `private`; never add helpers to the
  bare `WaveTurbulence` namespace (landing duplicate scan; see AGENTS.md).
- Docstrings: each main result names its source (`DH21 Lemma A.3 (L2808)` etc.).
- Conventions are yours to decide: endpoint cases, constants, `log(2K)` vs `log K`, the exact form of an
  inequality's error term, carrier choices for your own (non-frozen) helpers. Choose, document it in the docstring and
  handoff, and continue. Stop only for a genuine mathematical obstruction or a defect in a frozen statement.
- **Time alone is never a reason to stop** (this overrides "blocked > ~1 hour" in individual briefs): if a step takes
  long, keep going, commit partial results at milestones, and try alternative routes. Print `STOPPED` only for a genuine
  mathematical obstruction (a false statement, a missing idea after trying at least two routes) or a frozen-statement
  defect, with the exact obstruction written down.
- When the packet is done, or you are blocked, end with a line `READY <packet>` or `STOPPED <packet>: <reason>`,
  after a handoff in the AGENTS.md format. Then wait for the next instruction.

# Packet MAIN-GLUE — glue lemmas for sealing the frozen Theorem 1.1 (`WaveTurbulence.main`)

Read `COMMON.md` first. Source of the statements: `/home/scott/WaveTurbulence-dev/docs/campaign/orch/SEAL-PLAN.md` §B.4
(wt-orch's seal plan; read Part B fully). Worktree: `/home/scott/WaveTurbulence-worktrees/cumul`; new branch
`git switch -c w/main-glue main`. Files: `WaveTurbulence/Foundations/MainGlue/**` (namespace `WaveTurbulence.MainGlue`).
Build on the landed `Foundations/NLS/**` (reductions, `AkFlow`, `smoothDataSet`, `solvableEvent_eq_preimage`),
`Foundations/Probability/**` (`ae_initialCoeff_isRapidDecay`, `SchwartzLattice`), `Foundations/Gaussian/**`,
`Foundations/Cumulant/**`, and the frozen Wave A definitions.

Goals (the Wave-B-independent glue; do not end your turn at milestones):
1. **G5** (`HasLaw` from `Measurable` + `map`), **G7** (Σ_m φin(m/L) ≤ C L^d for L ≥ 1), **G6** (mass event bound),
   **G10** (parameter facts (a), (b), (c)) — the quick ones first.
2. **G1** `measurableSet_smoothDataSet` (route in SEAL-PLAN: forward/backward reductions, `IsRapidDecay` Borel with
   rational constants, the ℓ¹ flow's lower-semicontinuous existence time).
3. **G2** (a measurable observable Φ with ‖û(t,n)‖² = Φ c on the smooth-data set).
G4, G8, G9, G11 use Wave B objects (`AnsatzAt`, `Fev`) and wait for the Wave B freeze. State everything exactly as in
SEAL-PLAN §B.4 (or argue a better form in your handoff). Done: `READY main-glue`.

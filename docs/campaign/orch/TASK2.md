# wt-orch Task 2 — delta audit of the Wave A draft v2

Thank you for the Task 1 audit (committed on w/orch as 49d5f8b). The orchestrator applied:
- R1: `(∀ n, Measurable (g n))` added before `iIndepFun`.
- O2: new definition `kineticTime α = 1 / (2α²)` (source L297) and binders `∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →`
  replacing the repeated expressions; `φ (t / kineticTime α) …`.
- O3: `Ω : Type u` (universe-polymorphic).
- New: `weightedL2Norm` (⟨k⟩ = (1+|k|²)^{1/2}, GIT20 L549, since TARGET never defines ⟨k⟩) and theorem `wkelwp`
  (TARGET Prop `wkelwp`, L598–L606), so that Wave A also fixes τ_max and the main theorem's WKE hypothesis is
  known to be satisfiable for τ★ < τ_max.
Not applied: O1 (HasLaw; kept `P.map … = …` plus `Measurable`), O5 (non-dependent hyperplane formula — a lemma for
the WKE packet, not a definition change); O4 characterization lemmas are assigned to provers.

New file: `scratch/Draft-v2.lean` in your worktree (elaborates with two `sorry` warnings).

Task: refute-first delta audit of exactly the changed/new declarations (`kineticTime`, the new binders of `main`,
`weightedL2Norm`, `wkelwp`), same format as Task 1, file `docs/campaign/orch/audits/WaveA-v2-delta.md` on `w/orch`,
commit. For `wkelwp`: quantifier structure (∃ τmax : ℝ≥0∞ first), the iff (existence exactly below τ_max —
maximality), uniqueness on `[0, τ★]`, the blow-up formulation ("lim_{τ→τmax} = ∞" as ∀ M ∃ τ₀ < τmax ∀ τ★ ∈ (τ₀, τmax)
∀ solutions φ on [0, τ★], M < ‖⟨k⟩^s φ(τ★)‖), the standing assumption `3 ≤ d`, no sign assumption on φin (source:
"any Schwartz initial data"), and junk values (Bochner/sqrt). Then print `READY audit-waveA-v2` and wait.

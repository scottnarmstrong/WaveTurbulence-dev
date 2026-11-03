# wt-orch Task 6 — infra statement review 2, then the Wave B delta audit

`git merge main` first (your stage 1–3 audits are landed; the stage-3 audit by an independent auditor is
`docs/campaign/orch/audits/WaveB-stage3.md`).

## 6a (now): statement review of newly landed Foundations

Same method as Infra-review-1 (statements, not proofs; normalizations, junk values, dischargeable hypotheses,
uniformity of constants, the `ContDiff ℝ ⊤` = analytic pitfall F44). Modules landed since then:
`Foundations/Resonant/**`, `Foundations/Fourier/**` (χ₀ with F41, 𝔛 norms, restriction norms, Fourier-L¹ products),
`Foundations/WKE/**` (WKE-TAYLOR: existence, τ_max, `wkelwp_conj12`, Taylor expansion/bound), `Foundations/NLS/**`
(reduction, uniqueness, classed a-system), `Foundations/WeylSums/**` (Gauss sums), `Foundations/NumberTheory/**` and
`Foundations/Counting/**` (van der Corput toolkit; note the third-party salt code, docs/THIRD-PARTY.md),
`Foundations/Analysis/**`, `Foundations/LinAlg/**`, `Foundations/Combinatorics/**`, `Foundations/Probability/**`,
`Foundations/WKEL2/**` (partial). Priority: anything a frozen statement or a Wave B statement will consume directly
(the τ_max definition and `wkelwp_conj12` vs the frozen `wkelwp`; the NLS reduction vs the frozen
`IsSmoothNLSSolution`; χ₀ vs WAVE-B §2.6). File `docs/campaign/orch/audits/Infra-review-2.md`, commit, `READY task6a`.

## 6b (when announced): delta audit of the Wave B fixes

wt-gauss-hc is applying stage-1 R1, stage-2 R2–R4, stage-3 R1–R7 (R8: B1.12 deferred; R9: cumulantExpansion dropped)
in `/home/scott/wt-scratch/waveb/` with a changelog in its DESIGN.md. When I announce `waveb-fixes`, audit the delta
against all three audits (every REQUIRED item closed exactly; no new defects) → `WaveB-delta-1.md`.

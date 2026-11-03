# Packet NT-CIRCLE — revision 2 (2026-11-03, after your STOPPED report)

Your audit is correct and very useful (commit 3229554): F3 is revised accordingly in
`/home/scott/WaveTurbulence-dev/docs/FINDINGS.md` (F3, F31). Decision: no Huxley. We prove a circle-problem bound with
some exponent `e < 2/3` by van der Corput's method; exponent 2/3 is a stepping stone and already serves
`basiccount0`(1), (3) and `basiccount`(5). Same worktree, branch and file ownership as before
(`WaveTurbulence/Foundations/NumberTheory/**`, `WaveTurbulence/Foundations/Counting/**`), same hard rules.

Goals, in order (commit after each):
1. **Exponential-sum toolkit** (reusable): `ψ(x) = x − ⌊x⌋ − 1/2` and its truncated Fourier expansion with error
   (Vaaler or Erdős–Turán style, explicit constants); Kusmin–Landau (first-derivative test); van der Corput's
   second-derivative test; Weyl–van der Corput differencing (A-process).
2. **Circle problem with exponent 2/3**, uniformly in the center: `|#{n ∈ ℤ² : ‖n − c‖ ≤ Q} − πQ²| ≤ C Q^{2/3}`
   (Q ≥ 1, all c ∈ ℝ²).
3. **`basiccount0pre`** (1) second (elementary) branch and (2) `estcross` — these do not need the discrepancy.
4. **B-process** (Poisson summation + stationary phase for `∑ e(f(n))` with explicit error terms, van der Corput's
   Lemma; Titchmarsh, *Theory of the Riemann zeta-function* §5.9–5.13, or Graham–Kolesnik, *Van der Corput's method of
   exponential sums*, ch. 3) and an exponent pair giving `(κ+λ)/(1+κ) < 2/3` (e.g. (11/30, 16/30) → 27/41, or
   whichever pair has the simplest derivation; report the exponent). Then the **circle problem with that `e < 2/3`**
   and the annulus bound `basiccount0pre`(1) with `Q^e` in place of `Q^{7/11}`.
5. Redo your exponent audit for every use with the proved `e` and record it in your handoff.

Mine first: Mathlib (`Mathlib/NumberTheory/`, `Mathlib/Analysis/Fourier/PoissonSummation.lean`), Scott's repos
(KAM-dev, eth-constants, Frohlich-Spencer, Balaban, DOZZ). Commit at every milestone. When done: `READY nt-circle`;
blocked > ~1 hour on one ingredient: `STOPPED nt-circle: <reason>` with a proposed route.

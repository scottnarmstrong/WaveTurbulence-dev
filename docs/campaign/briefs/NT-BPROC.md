# Packet NT-BPROC — van der Corput's B-process (for NT-EXPSUM, FINDINGS F3)

Read `COMMON.md` first. Context: `/home/scott/WaveTurbulence-dev/docs/FINDINGS.md` F3 (we need a circle-problem
exponent e < 2/3; the A-process alone does not give it; the B-process does). wt-nt (packet NT-EXPSUM, files
`Foundations/NumberTheory/**`, `Foundations/Counting/**`) works on the A-process side and the transfer
"exponent pair ⇒ circle exponent"; you supply the B-process. Coordinate only through the orchestrator.
Worktree: `/home/scott/WaveTurbulence-worktrees/an-sob`; new branch `git switch -c w/bproc main`. Files:
`WaveTurbulence/Foundations/VdCB/**` (namespace `WaveTurbulence.VdCB`). Import (don't edit) the landed
`Foundations/NumberTheory/**` (Kusmin–Landau, second-derivative test, Weyl differencing; third-party salt code under
Apache 2.0, see docs/THIRD-PARTY.md), `Foundations/Fourier/**` (Poisson summation, stationary phase pieces).

Goals (commit after each; do not end your turn at milestones):
1. **Truncated Poisson summation for exponential sums** (van der Corput's lemma): for f with f′ monotone on [a,b] and
   α = f′(b) ≤ f′(a) = β, Σ_{a<n≤b} e(f(n)) = Σ_{α−η<ν<β+η} ∫_a^b e(f(x) − νx) dx + O(η⁻¹ + log(β−α+2)) (Titchmarsh,
   *The theory of the Riemann zeta-function*, Lemma 4.7; or Graham–Kolesnik, *Van der Corput's method of exponential
   sums*, Lemma 3.5 — state the version you prove precisely).
2. **Stationary phase for the resulting integrals** with explicit error terms (Titchmarsh Lemma 4.6 / Graham–Kolesnik
   Lemma 3.6): ∫ e(g(x)) dx at a nondegenerate stationary point, with second- and third-derivative error terms.
3. **The B-process**: Σ e(f(n)) = Σ_ν e(f(x_ν) − νx_ν + 1/8)/√(f″(x_ν)) + error terms (Graham–Kolesnik Lemma 3.6 /
   Theorem 3.8 form), and the exponent-pair transform B(κ,λ) = (λ − 1/2, κ + 1/2) in the form wt-nt needs
   (report the exact statement so the orchestrator can relay it).
Done: `READY bproc`.

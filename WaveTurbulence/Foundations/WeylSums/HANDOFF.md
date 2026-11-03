# GAUSSSUM completed handoff — 2026-11-03

NT.dirichlet and both requested forms of NT.gaussSum are proved. No Hua work was started.
Branch: `w/gausssum`. All authored changes are within `WaveTurbulence/Foundations/WeylSums/`.
The integration instruction was followed: `git merge main`, merge commit `e84e2fa`.

## Public entry points

- Import `WaveTurbulence.Foundations.WeylSums.Dirichlet`:
  `WaveTurbulence.WeylSums.exists_coprime_approx` gives, for real `t` and natural `K ≥ 1`,
  integers `a` and positive natural `q ≤ K`, with `a.natAbs.Coprime q` and
  `|t-a/q| ≤ 1/(qK)`.
- Import `WaveTurbulence.Foundations.WeylSums.SharpInterval`:
  `norm_gaussSum_le_of_approx` proves, uniformly in real `s,r` and integer `h`,

      ‖gaussSum s r h K‖ ≤ 128 K (1 + log K) /
        (sqrt q * (1 + K * sqrt |s-a/q|))

  for natural `1 ≤ q ≤ K`, coprime integer `a`, and `|s-a/q| ≤ 1/(qK)`.
  `gaussSum` includes both integer endpoints `h,…,h+K`.
- Import `WaveTurbulence.Foundations.WeylSums.SmoothCutoff`:
  `exists_norm_smoothGaussSum_le` proves, for **every** fixed `χ : ℝ → ℂ` with
  `HasCompactSupport χ` and `ContDiff ℝ ∞ χ`, the existence of `Cχ > 0` such that

      ‖Σ_{n∈ℤ} χ((n-h)/L) e(s n² + r n)‖ ≤
        Cχ L / (sqrt q * (1 + L * sqrt |s-a/q|))

  uniformly in real `L ≥ 1`, real `s,r`, integer `h,a`, and natural `1 ≤ q ≤ L`,
  under coprimality and `|s-a/q| ≤ 1/(qL)`. There is **no logarithmic factor**.
  `smoothGaussSum` represents the lattice sum by `tsum`. The Gaussian Fourier
  superposition is justified by an explicit `HasSum` theorem, not by a convention
  that assigns zero to a divergent series. The uniform quantifiers give the
  requested bound on the supremum over `h,r` without requiring a separate supremum API.

No root import was added; root imports remain the orchestrator's responsibility.

## Files and approach

- `Dirichlet.lean`: Mathlib supplies the stronger error `1/((K+1)q)`; denominator
  monotonicity gives the requested version. Commit `9bd4ca9` (previously landed).
- `Basic.lean`, `Geometric.lean`, `Differencing.lean`, `RationalSpacing.lean`:
  exposed phase and sum definitions, translations, squaring/correlations,
  geometric inverse-distance bounds, and rational separation (previously landed).
- `ReciprocalCounting.lean`, `ResidueBlocks.lean`, `RationalResidues.lean`,
  `RationalCounting.lean`, `SharpCounting.lean`, `GaussAlgebra.lean`, `SharpInterval.lean`:
  reindex into residue-numerator fibers. The far fibers have harmonic total mass;
  the near fibers are affine progressions with step `q(s-a/q)`. A closest-point
  argument bounds the capped reciprocals by one capped term plus harmonic tails.
  Combine coarse `K²/q` and refined `1/(q|s-a/q|)` bounds, then take square roots.
  Milestones `40e68c6`, `c5cc08e` (sharp interval bound).
- `CompleteGauss.lean`, `RationalCompletion.lean`: exact finite Fourier completion.
  Squaring the complete sum and character orthogonality bound its squared norm by
  `2q`. The doubling kernel has at most two points, so even moduli are included.
  Completion coefficients have norm at most `sqrt 2 / sqrt q`.
- `GaussianLattice.lean`, `ResidueLattice.lean`, `GaussianPoisson.lean`,
  `GaussianCompletion.lean`: exact complex Gaussian Poisson formula, merging the
  residue/quotient dual lattices by an explicit equivalence with `ℤ`, then uniformly
  bounding the shifted Gaussian tails. Milestone `7eae20d`.
- `GaussianDamping.lean`, `GaussianBound.lean`: for damping `L⁻²-2iβ`, the approximation
  guarantees that the **merged** dual lattice has decay coefficient at least `1/5`.
  Its prefactor is at most `2L/(1+L sqrt |β|)`. This gives the log-free Gaussian bound.
- `CutoffFourier.lean`, `GaussianSuperposition.lean`, `SmoothCutoff.lean`:
  `ψ(x)=χ(x)exp(πx²)` is smooth and compactly supported, hence Schwartz. Fourier
  inversion writes `χ` as a Gaussian times linear phases with integrable weight
  `F=Fourier(ψ)`. Absolute Gaussian domination justifies exchanging sum and integral.
  Apply the Gaussian bound uniformly in the shifted linear frequency and integrate
  `‖F‖`. One admissible constant is the absolute Gaussian constant times
  `1 + ∫ ‖F‖`. This uses no stationary-phase black box and preserves dependence on
  the fixed cutoff only. The smooth-bound commit accompanies this handoff.

## Exact checks and output

Targeted builds were run sequentially through the `wt-throttled` override:

- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.Dirichlet`
  — `Build completed successfully (1902 jobs).`
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.SharpInterval`
  — `Build completed successfully (3561 jobs).`
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.SmoothCutoff`
  — `Build completed successfully (3812 jobs).`

These job counts include cached dependencies; no Mathlib rebuild or whole-library
build was requested. All final modules compile without warnings and at default budgets.
All Lean files are below 1500 lines (largest: 222 lines).

`nice -n 5 lake env lean /home/scott/wt-scratch/gausssum/AuditFinal.lean`
imports the three entry points and prints axioms for:

- `exists_coprime_approx`
- `norm_gaussSum_le_of_approx`
- `exists_norm_smoothGaussSum_le`
- `norm_completeGauss_sq_le`
- `quadratic_completion`
- `norm_gaussianQuadraticSum_le`
- `exists_gaussian_fourier_representation`
- `hasSum_gaussian_fourier`

Each reports exactly `[propext, Classical.choice, Quot.sound]`.
Earlier scratch audits are `AuditDirichlet.lean`, `AuditIngredients.lean`,
`AuditCounting.lean`, and `AuditSharp.lean` in the same scratch directory.

`git diff --check` and the staged whitespace check pass. A search in all owned
Lean files finds no `sorry`, `axiom`, `admit`, `unsafe`, `opaque`, or `set_option`.
There are no frozen/provider imports or edits to frozen files, the manifest,
findings ledger, or other workers' modules. Intermediate elaboration failures
were repaired; none remain in the final checks.

## Conventions, source findings, and uncertainties

- Per the orchestrator's ruling, the standalone sharp interval estimate uses
  **`1 + log K`**, equivalent up to an absolute constant to `log(2K)`, positive
  at `K=1`, and comparable to `log K` for `K≥2`. The source DH23 L1129 instead
  writes `K log L` at the ambient scale. The docstrings record this convention.
  The earlier endpoint concern is resolved and is not a blocker.
- The earlier candidate source wording issue remains: DH23 L1127 restricts
  `0≤a<q≤K`, then L1131 says every `s∈[0,1]` admits such an approximation.
  For `s=1`, `K>1`, this needs periodic interpretation or allowance of `a=q=1`.
  The implemented theorems allow arbitrary integer numerators, as goal 1 requests.
- The source supremum is supplied as a uniform bound for every `h,r`; no separate
  supremum definition is introduced. Complex cutoffs and real scales are allowed.
- No remaining mathematical uncertainty or unproved input in NT1. No optional Hua
  work, campaign-wide closure claim, or root integration is included.

READY gausssum

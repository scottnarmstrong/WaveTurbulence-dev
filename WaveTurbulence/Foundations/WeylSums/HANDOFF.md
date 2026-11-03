# GAUSSSUM partial handoff — 2026-11-03

NT.dirichlet is complete. NT.gaussSum is **not proved**. No Hua work was started.

## Files and commits

All files are under `WaveTurbulence/Foundations/WeylSums/` on `w/gausssum`.

- `Dirichlet.lean`: `exists_coprime_approx`, giving integer numerator, positive natural denominator,
  coprimality, `q ≤ K`, and error at most `1/(qK)` for every real `t` and natural `K ≥ 1`.
  Commit `9bd4ca9`.
- `Basic.lean`: exposed additive exponential `e`, linear sums, inclusive quadratic sums,
  trivial bounds, translation identity, nonresonant geometric-series bound.
- `Geometric.lean`: exponential periodicity, `4‖t : AddCircle 1‖ ≤ ‖e(t)-1‖`, and
  `‖linearSum t N‖ ≤ min(N, 1/(2‖t : AddCircle 1‖))` for nonintegral frequency.
- `Differencing.lean`: triangular reindexing, exact square expansion, quadratic correlation identity,
  and `norm_gaussSum_sq_le_differencing`, uniformly in shift and linear coefficient.
  These three files first committed in `4e077c0`.
- `RationalSpacing.lean`: rational spacing `1/q ≤ ‖m/q : AddCircle 1‖` when `q ∤ m`,
  the coprime-multiple corollary, and its quantitative perturbation inequality.
- `Basic.lean` additionally proves `gaussSum_zero_phase` and `not_gaussSum_bound_log_one`:
  the literal endpoint of the requested `K log K` estimate fails.

## Approach and outstanding mathematics

Mathlib's Dirichlet theorem supplies the stronger error `1/((K+1)q)`. The wrapper weakens this
by denominator monotonicity. Searches in Mathlib and the local KAM-dev and ETH/eth-constants
repositories found no reusable incomplete quadratic Weyl estimate. Mathlib's `NumberTheory/GaussSum`
concerns multiplicative/additive character sums on finite fields, rather than the needed interval sums.

The interval convention is exactly DH23's inclusive `p=h,…,h+n`, implemented using `range (n+1)`.
Squaring, reindexing by positive differences, and taking norms gives

    ‖G_h(s,r,n)‖² ≤ n+1 + 2 Σ_{d=0}^n ‖linearSum (2s(d+1)) (n-d)‖.

The geometric bound is proved separately with a nonintegrality hypothesis: at integer frequency
one must use the trivial bound, because the inverse of zero in Lean is zero.

Still missing: a rational-approximation counting estimate for these near-resonant linear frequencies
that retains the dependence on `β = |s-a/q|`. Neither the full sharp interval bound nor the smooth
bound has been installed as a Lean theorem, assumption, or placeholder. Rational spacing alone does
not prove the required harmonic counting estimate.

Proposed continuation after the endpoint convention is settled: sum the capped inverse-distance
bounds over rational residue blocks, treating exact resonances separately, to obtain the sharp
interval estimate with `log(2K)` (or keep the source's ambient `log L`). For the target's **log-free**
smooth estimate, use rational Fourier completion and Poisson/stationary phase with decaying tails;
summation by parts from the logarithmic sharp estimate alone does not remove that logarithm.

The intended generic smooth statement, still unproved, is: for every fixed
`χ : ℝ → ℂ` with `ContDiff ℝ ∞ χ` and compact support, there is `Cχ > 0` such that, for
`L ≥ 1`, `1 ≤ q ≤ L`, coprime `a,q`, and `|t-a/q| ≤ 1/(qL)`, uniformly in
`h : ℤ` and `ρ : ℝ`,

    |Σ_{x∈ℤ} χ((x-h)/L) e(tx²+ρx)| ≤ Cχ L / (√q (1+L√|t-a/q|)).

Compact support makes the displayed sum finite. The constant may depend on the cutoff, including
its support and derivative bounds; it cannot be universal over arbitrary cutoffs.

## Checks

Final targeted builds (through the `wt-throttled` override, sequentially):

- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.Dirichlet` — `Build completed successfully (1902 jobs).`
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.Geometric` — `Build completed successfully (2290 jobs).`, includes Basic.
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.Differencing` — `Build completed successfully (2005 jobs).`
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.RationalSpacing` — `Build completed successfully (1920 jobs).`

Scratch audit commands:

- `nice -n 5 lake env lean /home/scott/wt-scratch/gausssum/AuditDirichlet.lean`.
- `nice -n 5 lake env lean /home/scott/wt-scratch/gausssum/AuditIngredients.lean`.

For the Dirichlet wrapper, main differencing inequality, inverse-distance minimum bound,
exponential separation inequality, shift identity, rational-spacing results, and endpoint counterexample,
`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

`git diff --check` is clean. No forbidden declarations, placeholders, budget overrides,
frozen/provider imports, root changes, or edits to other workers' files. No Mathlib compilation or
whole-library build was requested. Intermediate elaboration errors were fixed; the final builds
have no warnings. Sources and the findings ledger were left unchanged.

## Suspected errata and deviations

1. **Brief/blueprint endpoint defect:** `K log K` vanishes at `K=1`. With `s=r=0`, `h=0`,
   `a=0`, `q=K=1`, the inclusive sum has norm `2`, contradicting every such bound regardless of
   the implicit constant. `not_gaussSum_bound_log_one` checks this in Lean. DH23 L1129 instead says
   `K log L`, with large ambient `L`; this finding is not a refutation of that source bound.
   Suggested repair for the standalone packet statement: `K ≥ 2` or `log(2K)`. No replacement
   source-facing estimate has been silently introduced.
2. **DH23 L1127–L1131:** “`0≤a<q≤K`” followed by “`s∈[0,1]` can be approximated by such rational
   number.” At `s=1`, `K>1`, every `a<q` has error at least `1/q > 1/(qK)`. This needs a periodic
   interpretation or allowance of `a=q=1`. The implemented Dirichlet wrapper has unrestricted
   integer numerator, as requested in goal 1, so avoids the problem. Candidate source wording defect.

STOPPED gausssum: the literal K=1 logarithmic bound is false; the full rational-approximation counting and smooth-cutoff proofs remain open.

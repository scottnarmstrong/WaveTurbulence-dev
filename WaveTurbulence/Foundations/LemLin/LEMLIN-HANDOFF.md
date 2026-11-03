# LEMLIN (NT10) handoff

Both goals are proved. Branch `w/lemlin`, worktree
`/home/scott/WaveTurbulence-worktrees/cumul`. Integrated main `627f129`
through merge `876a13f`. All worker changes are confined to this directory.
Root imports, frozen files, providers, manifest and campaign ledgers were not edited.

## Public entry points and files

All declarations below are in `WaveTurbulence.LemLin`.

- `LinearEstimate.lean`: `lemlin` proves TARGET L1536–L1543 with a
  dimension/cutoff-dependent constant and the stated minimum.
  `lemlin_lower_momentum_bound` separately proves the additional F23
  consequence `C_d L^(d+1)` using `‖r‖ ≥ L⁻¹`.
- `LinearRescale.lean`: `lemlin_unit_time_lower_bound` proves the unit-time
  bound `C_d L^(d+1) / (δ L^(2γ))`, equivalently
  `C_d δ⁻¹ L^(d+1−2γ)`. The source's convention with `π` in place of
  `2π` is obtained by applying this theorem with `δ/2`, costing a factor 2.
- `CubicVector.lean`: `lemcubic0_vector` proves TARGET L1544–L1553 in
  three-vector coordinates, for both explicit choices of `vectorLambda`.
  Its conclusion includes `Summable` of the absolute integral values and
  the bound `K_d / (1+|s|+|t|)^d`.
- `CubicEstimate.lean`: `lemcubic0` gives the same result with spatial
  coordinates grouped first. `CubicTensor.lean` factors the actual integral;
  `Transpose.lean` and `CubicVector.lean` prove exact equality with the
  vector-first source integral, including volume preservation and the
  frequency-index bijection.

Supporting modules:

- Linear: `LinearSum`, `ScalarPoisson`, `ScalarFinite`, `Periodization`,
  `ScalarPeriod`, `ScalarFlow`, `TensorFactorization`, `LargestCoordinate`,
  `TrivialWindow`, `WindowParameters`, `LinearWindow`.
- Cubic amplitudes and calculus: `ScalarCutoff`, `CubicAmplitude`,
  `CubicTranslation`, `FiniteFubini`, `CoordinateFourier`,
  `QuadraticDerivative`, `CubicDerivative`, `CubicMatrix`.
- Cubic estimates and summation: `AffineFourier`, `FourierEnvelope`,
  `CubicEnvelope`, `ScalarStationary`, `CubicFrequency`, `CubicMomentStep`,
  `CubicMoments`, `CubicWeight`, `LatticeTail`, `ProductSummation`,
  `ScalarLattice`.

There are 36 Lean modules, 2697 lines in total; the largest is 128 lines.
Every module has the required module/interface shape. Every body is proved;
there are no placeholders, custom axioms, budget overrides or quarantined imports.

## Approach

The linear sum has fixed finite support and factors into scalar sums. All
but one coordinate cost `3L`. Scalar Poisson summation bounds the remaining
sum by a nonnegative periodization of the fixed cutoff's Fourier transform.
Tonelli and partitioning the real line into translated cells show that one
frequency period has mass at most `L` times the fixed Fourier L¹ mass.
Changing variables along the largest momentum coordinate gives cancellation
`C_d L^d / ‖r‖`. The source parameter bounds imply that the time interval's
frequency image fits in one period. Combine with the elementary bound and
then apply the lower momentum bound for F23.

For the cubic result, translation changes only a unit phase and linear
frequencies. Integrating in `x` gives the same nonnegative Fourier envelope
for both quadratic forms. Integrating this envelope in `y` or `z` gives
respectively the reciprocal `|t|` or `|s|` gain. Combining these with the
uniform mass bound proves scalar decay at scale `Γ=1+|s|+|t|`.
Coordinate integration by parts uses the actual frozen `partialDeriv` and
expresses a frequency factor through one differentiated cutoff and three
coordinate-weighted cutoffs. These remain smooth with fixed support.
Induction proves arbitrary frequency moments while retaining stationary
decay. Six moments give a product of three rational tail weights. Since
`|s|,|t| ≤ L` and `L ≥ 1`, the rescaled lattice spacing is at least `1/3`;
a floor translation gives a uniform, genuinely summable scalar majorant.
Two finite-product summation arguments give the scalar frequency sum and
its tensorized d-dimensional version. The explicit source integral factors
by product Lebesgue Fubini, and the vector-coordinate wrapper preserves both
volume and the integer-frequency index set.

## Statements, premises and deviations

- The linear root is stronger than the source in its momentum domain:
  it allows all real momenta in the norm range, rather than requiring a
  lattice momentum. No cancellation step needs lattice membership of `r`.
- Source standing smallness/large-size assumptions are made explicit as
  `L ≥ 1`, `0 ≤ δ ≤ 1`, and `γ+η ≤ 1`. The unit-time corollary requires
  `δ > 0` for division. The proof works without separate `0<γ<1` or `d≥3`
  hypotheses once these sufficient quantitative conditions hold.
- The cubic theorem likewise works for every natural dimension, under the
  explicit large-size consequence `L ≥ 1`; it includes both source phases
  and is uniform in all six translation/modulation vectors.
- The fixed cutoff is the landed `Fourier.chi0` and its tensor product.
  All smoothness statements use `ContDiff ℝ ∞` with the `ContDiff` scope.
- Physical integration uses ordinary finite-product Lebesgue measure.
  `cubicVectorIntegral` is the full integral on three vector blocks;
  `vectorLambda` is exactly `x·z` or `z·(x+y−z)`.
- F23's extra estimate is a separate proved theorem, not a new assumption.
  No additional source premises or conclusion-shaped hypotheses enter the roots.

## Checks

Executed one targeted compile invocation at a time through `wt-throttled`.
Final root checks (after merging main):

```
nice -n 5 lake build WaveTurbulence.Foundations.LemLin.CubicVector
Build completed successfully (9093 jobs).

nice -n 5 lake build WaveTurbulence.Foundations.LemLin.LinearRescale
Build completed successfully (9090 jobs).
```

These two roots cover every owned Lean module.

Axiom audit command:

```
nice -n 5 lake env lean /home/scott/wt-scratch/lemlin/FinalAxioms.lean
```

Each of `lemlin`, `lemlin_lower_momentum_bound`,
`lemlin_unit_time_lower_bound`, `lemcubic0`, `lemcubic0_vector`, and
`scalarCubic_lattice_sum` prints exactly:

```
[propext, Classical.choice, Quot.sound]
```

No custom or placeholder axioms occur.

Other exact checks:

```
python3 /home/scott/.codex/skills/lean-project-architecture/scripts/check_lean_modules.py --root /home/scott/WaveTurbulence-worktrees/cumul
check_lean_modules: PASS (439 Lean files, 0 comparator configurations)

python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json
FROZEN-ANCHOR GUARD OK

git diff --cached --check
(no output, exit 0)
```

Scope check against integrated main: `PASS`, only this directory changed. No whole-library or Mathlib rebuild,
clean, toolchain update or budget override was run.

## Suspected source errata

Pinned source:
`/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`.

1. L1541–L1542, proof of `lemlin`: after the Poisson identity with prefactor
   `L^d`, the sentence “the left hand side ... is bounded by” introduces
   `(lemlin3)` without that prefactor. That displayed majorant needs the
   factor `L^d` to recover `(lemlin2)`. The formal proof retains it.
2. L1542, the stated decay `(|g^1|+L)^(-5d)` “for all but one choice of
   `g^1`” is written in an absolute frequency index despite arbitrary
   `τ,ξ`. Such a tail needs recentering of the integer frequency index for
   the claimed uniformity. The formal proof instead integrates the full
   periodized Fourier mass, which is invariant under the frequency shift.

These concern the written proof, not the validity of either lemma statement.
The brief's existing F23 omission is addressed by the two separate lower-bound
corollaries. No unresolved mathematical or Lean obligations remain.

READY lemlin

# MISC-A handoff

Completed goals 1–5. Goal 6 (DH21 Hua) was explicitly transferred to NT2 by the orchestrator and is excluded.
Branch: `w/misc-a`, in `/home/scott/WaveTurbulence-worktrees/cumul`.
Validated code snapshot: `95bddf3`, after merging main `fb1a670` in `9c0abf0`.

## Files and entry points

All packet Lean files are under `WaveTurbulence/Foundations/` (26 modules).

- `LinAlg/MaxVolume.lean`, `LinAlg/BoundedSpanning.lean`: TARGET A.7. Entry point
  `WaveTurbulence.LinAlg.exists_bounded_spanning_selection`.
- `LinAlg/FiniteRepresentatives.lean`, `LinAlg/LatticeObservations.lean`,
  `LinAlg/LatticeRepresentatives.lean`: finite records and polynomial representative count.
- `LinAlg/GramResidual.lean`, `LinAlg/OrthogonalResidualFamily.lean`,
  `LinAlg/IntegerGramResidual.lean`, `LinAlg/IntegerOrthogonalSelection.lean`,
  `LinAlg/LatticeRescaling.lean`, `LinAlg/LatticeRepresentation.lean`,
  `LinAlg/FiniteRepresentation.lean`: TARGET A.6. Combined entry point
  `WaveTurbulence.LinAlg.exists_uniform_finite_lattice_representation`.
- `Combinatorics/BinomialConvolution.lean`, `Combinatorics/MultiVandermonde.lean`,
  `Combinatorics/FactorialSplitting.lean`: DH21 A.4. Entry point
  `WaveTurbulence.Combinatorics.factorialSplitSum_nine_le`.
- `Combinatorics/PartitionCount.lean`, `Probability/CumulantMomentBounds.lean`:
  factorial moment–cumulant conversions.
- `Probability/MomentTails.lean`, `Probability/RestrictedCauchySchwarz.lean`,
  `Probability/RestrictedProducts.lean`, `Probability/GaussianEvents.lean`:
  even-moment tails, countable unions, restricted Cauchy–Schwarz, Gaussian event bounds.
- `Probability/GaussianSummability.lean`, `Probability/SchwartzLattice.lean`,
  `Probability/WeightedLatticeSummability.lean`, `Probability/RandomRapidDecay.lean`,
  `Probability/SmoothData.lean`: initial-data summability and smoothness. Entry point
  `WaveTurbulence.Probability.ae_summable_all_real_weights_and_smooth`.

The A.7 export was moved from the bare namespace to `WaveTurbulence.LinAlg` after the updated namespace rule.
No downstream reference to the former name existed. Frozen files and the root import file were not edited by
this packet; the main merge incorporated the orchestrator's root imports.

## Approach and source correspondence

- TARGET A.7, L2449–L2457: choose a globally maximal absolute determinant in the span of the finite set.
  Column replacement gives the stronger coefficient bound one. The source-facing result retains `2^(d-1)`.
  Empty sets and zero-dimensional spans are covered.
- TARGET A.6, L2435–L2445: Cramer's rule clears the Gram-projection denominators. Integer residuals form a
  nonzero orthogonal family with the same span and bounds `(d+1)! B^(2d+1)`, including for a linear functional
  bounded only on the input vectors. Correct lattice rescaling uses `B=M^3`. Finite representatives are
  selected from records of at most `d` test vectors and their bounded pairing values. The count is
  `M^(4d²+6d)`. The combined theorem chooses one exponent before `L`, `M`, and `k`, so it depends only on `d`.
  Both vector norms and the Euclidean norm of the value vector are bounded; the latter is explicitly
  `latticePoint (L^2) m`, hence lies in `(L^-2 ℤ)^q`.
- DH21 A.4, L2814–L2822: the binomial-ratio sum is at most four. A polynomial expansion proves weighted
  multivariate Vandermonde with no dimension loss. Eight iterations give constant `4^8 = 65536` for nine
  groups. The exported sum uses the paper's iterated-binomial enumeration: `factorialSplitSum n` has
  `n+1` groups. The binomial coefficients telescope to the source multinomial coefficient, and each
  decomposition is enumerated once. There is no separate flat nine-tuple front end.
- TARGET L813–L819: event expectations always use the unnormalized restricted measure. The two
  Cauchy–Schwarz estimates cover product moments and small-event factors. The Gaussian fourth absolute
  moment is two, yielding `sqrt 2 * sqrt (P.real A)`. Partition coding gives at most `n^n` partitions and
  weighted count at most `(2n)!`. Conditional blockwise factorial bounds with constant `C₀` convert in
  either direction with constant `C₀+2`; these helpers do not assert moment estimates for a PDE field.
- TARGET (DAT), L290–L293: the square root of a Schwartz envelope is rapidly decaying on the lattice,
  without needing smoothness of the square root. Summable deterministic weights times Gaussian absolute
  values are summable almost surely by summable L¹ norms. All natural weights hold on one full-measure
  event, giving rapid decay, then every real Japanese-bracket weight and a C∞ torus series on that same
  event. Independence is not needed. The frozen `initialCoeff` and the landed torus synthesis API are used.
  Smoothness is `ContDiff ℝ ∞` with the `ContDiff` scope, not the analytic order `⊤`.

## Checks

Each command was run separately through `wt-throttled`; no whole-library or Mathlib rebuild was run.
Final successful targeted builds (all ended with `Build completed successfully` and no warnings):

```text
nice -n 5 lake build WaveTurbulence.Foundations.LinAlg.BoundedSpanning
  Build completed successfully (9049 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.LinAlg.FiniteRepresentation
  Build completed successfully (9059 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Combinatorics.FactorialSplitting
  Build completed successfully (3139 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Probability.CumulantMomentBounds
  Build completed successfully (3567 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Probability.GaussianEvents
  Build completed successfully (9051 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Probability.RestrictedProducts
  Build completed successfully (3538 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Probability.MomentTails
  Build completed successfully (3326 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.Probability.SmoothData
  Build completed successfully (9068 jobs).
```

The main merge changed none of the frozen definitions, Gaussian/Cumulant/Torus dependencies, Lake configuration,
or toolchain used by these builds. The namespace change was rebuilt after the merge.

```text
nice -n 5 lake env lean /home/scott/wt-scratch/misc-a/PacketAxioms.lean
  exit 0; all 15 axiom checks below passed, plus an exact-type consumption example
  for simultaneous real-weight summability and C∞ smoothness.
python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json
  FROZEN-ANCHOR GUARD OK
python3 /home/scott/.codex/skills/lean-project-architecture/scripts/check_lean_modules.py --root /home/scott/WaveTurbulence-worktrees/cumul
  check_lean_modules: PASS (301 Lean files, 0 comparator configurations)
git diff --check
  exit 0, no output
```

A word-boundary scan of all packet Lean files found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, or
budget overrides. No forbidden theorem/provider imports occur.

## Axioms

`#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]` for each of:

```text
WaveTurbulence.LinAlg.exists_bounded_spanning_selection
WaveTurbulence.LinAlg.exists_uniform_finite_lattice_representation
WaveTurbulence.LinAlg.exists_lattice_representation
WaveTurbulence.LinAlg.exists_lattice_representatives
WaveTurbulence.Combinatorics.factorialSplitSum_nine_le
WaveTurbulence.Probability.measureReal_norm_ge_le_even_moment
WaveTurbulence.Probability.measure_iUnion_norm_ge_le_lintegral
WaveTurbulence.Probability.norm_setIntegral_le_sqrt_measure_mul
WaveTurbulence.Probability.norm_integral_mul_restrict_le
WaveTurbulence.Probability.integral_norm_sq_restrict_le
WaveTurbulence.Probability.norm_cumulant_le_of_moment_bounds
WaveTurbulence.Probability.norm_moment_le_of_cumulant_bounds
WaveTurbulence.Probability.ae_summable_weighted_gaussian
WaveTurbulence.Probability.ae_initialCoeff_isRapidDecay
WaveTurbulence.Probability.ae_summable_all_real_weights_and_smooth
```

## Conventions, suspected errata, and uncertainties

1. A.6 uses `2 ≤ L ≤ M`, the ambient large-box convention. The literal source says “Fix `M≥L`” and
   “at most `M^{C₀}` elements.” At `d=1`, `L=M=1`, the functionals `k=0` and `k=2` already require different
   representatives (test `z=1`), contradicting a bound of one. The convention is documented in the Lean
   source and is within COMMON.md's authorization to choose endpoint conventions.
2. TARGET L819 ends its displayed estimate with `C₀ L^d P(F_p^c)`. The preceding Cauchy–Schwarz step only
   gives `C₀ L^d sqrt(P(F_p^c))`; the square root appears to have been dropped. The proved Gaussian estimate
   retains the square root. The corrected bound still tends to zero under the stated exceptional-event decay.
3. Outside this packet after the scope transfer: DH21 Hua's inclusive sum has one term when `n=0`, so the
   printed `n²` and `n⁴` bounds need `n≥1` or an `n+1` convention if the paper's `ℕ` includes zero.
   No Hua files were edited or implemented here.
4. A.7 uses global maximal volume rather than the source's successive-volume proof; its bound is stronger.
   A.4 uses equivalent iterated-binomial summation rather than a separate flat-tuple API.

No unresolved mathematical or Lean proof gaps remain in goals 1–5. These are implementation exports for the
orchestrator's integration; no frozen theorem was edited or sealed and no graph node was marked PROVED here.

## Commits

Packet milestones: `9d76d49`, `f437996`, `4adc150`, `3804551`, `5627a38`, `8b7548f`, `5f9cf81`, `0587ef3`.
Main integration: `9c0abf0`. Final namespace alignment: `95bddf3`.

READY misc-a

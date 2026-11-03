# MAIN-GLUE handoff

All assigned goals G5, G7, G6, G10(a,b,c), G1 and G2 are proved.
Branch: `w/main-glue`; worktree: `/home/scott/WaveTurbulence-worktrees/cumul`.
Integrated main `a51ef47` through merge `cbccbb2` before final verification.
Only `WaveTurbulence/Foundations/MainGlue/**` differs from integrated main.

## Files and entry points

Import `WaveTurbulence.Foundations.MainGlue.SealInputs` for the full packet.
All declarations are in `WaveTurbulence.MainGlue`.

| Goal | File | Main declarations |
|---|---|---|
| G5 | `GaussianLaw.lean` | `hasLaw_stdComplexGaussian` |
| G7 | `LatticeSum.lean` | `summable_schwartz_lattice`, `schwartz_lattice_sum_le` |
| G6, general weights | `MassEvent.lean` | `integral_gaussian_mass_restrict_le` |
| G6, source profile | `SchwartzMass.lean` | `integral_initial_mass_restrict_le`, `initial_mass_event_bound` |
| G10(a,b) | `DiscreteParameters.lean` | `ceiling_subdivision`, `log_pow_le_final_exponent` |
| G10(c), general gap | `Absorption.lean` | `eventually_absorb`, `probability_tail_le_power` |
| G10(a,c), source parameters | `InductionParameters.lean` | `induction_exponent_gap`, `eventually_final_exponent`, `induction_error_absorption_final` |
| G1 | `SmoothData.lean` | `measurableSet_smoothDataSet` |
| G2 | `Observable.lean` | `measurable_fourierEnergyObservable`, `fourierEnergyObservable_eq`, `exists_measurable_fourier_energy` |
| interface | `SealInputs.lean` | public imports of all packet inputs |

Ten Lean modules, 609 lines total; largest file: 106 lines.

## Approach

G5 packages the frozen measurability and pushforward hypotheses as Mathlib
`HasLaw`, without adding a probability or independence premise.

G7 uses landed multidimensional Poisson summation. The factor is exactly
`L^d`; Schwartz decay bounds the dual samples at `Lm` by a fixed summable
integer-lattice majorant when `L ≥ 1`. The resulting constant depends only
on the profile and dimension. Sampling convergence is proved separately
for every positive `L`, so the real series is substantive.

G6 applies the landed Gaussian fourth-moment event bound termwise.
Summability of the deterministic weights controls the integrals of the
norms, allowing the Bochner integral to commute with the infinite series.
The general result needs no independence and applies to every event `A`.
The source-profile wrapper supplies actual summability via G7 and preserves
the unnormalized restriction `P.restrict A`. The combined bound chooses
`C` before the probability space, random family, and event.

G10(b) proves the exact ceiling construction with `D : ℕ` and `δ=τ/D`:
`1 ≤ D`, `0<δ≤δ₀`, and `τ=Dδ`. G10(a) proves the floor-power lower bound
and supplies a large-size threshold. For G10(c), the logarithmic probability
tail beats `L^(-θ-1)` after multiplication by `L^d`. The remaining relative
errors are bounded by `2 L^(-ε) + 2√2 C L^(-1)`, which tend to zero. The
source specialization proves a uniform positive gap for every `p≤D` and
substitutes the actual final floor-power exponent.

G1 reuses the landed `NLS.Measurability` proof. That proof describes the
smooth-data set using rapid decay, integer-radius truncated flows, and
closed ball conditions; the weighting map is measurable via finite
truncations. Our wrapper chooses `δ=1`, rescaled terminal time
`T / kineticTime (L^(-γ))`, and has exactly the proposed physical-time
premises `0<L`, `0<T`, `α=L^(-γ)`.

G2 chooses an actual smooth solution on the smooth-data set and defines
the Fourier-energy observable to be zero outside that set. The deterministic
landed NLS selection theorem proves this observable measurable: coordinate
data and a unit envelope realize the identity coefficient map. No Gaussian
law or Schwartz property of that auxiliary envelope is needed by the
landed measurability theorem. NLS uniqueness then proves equality with
every smooth solution of the prescribed coefficients, giving precisely
the existential observable requested in SEAL-PLAN §B.4.

## Necessary correction to SEAL-PLAN G10(c)

SEAL-PLAN §B.4(c) writes the threshold as `L₁(d,η,φin)`, while its exponent
gap is `η^20 2^(-D)`. Dependence on the finite induction length `D` (or on
a specified positive lower bound for this gap) is necessary.

For fixed `L>1` and `θ>0`, take the nonnegative mass constant `C=0` and
`p=D`. The ratio of the first error term to the desired bound is

`2 L^(-θ(1+2^(-D))) / L^(-θ) = 2 exp(-θ 2^(-D) log L) → 2`.

Thus no threshold independent of unbounded `D` can absorb even that first
term. `induction_error_absorption_final` explicitly chooses its threshold
after `d,η,C,D`. This is compatible with the frozen main theorem, where
`L₀` is chosen after the profile, terminal time, solution, and hence the
subdivision length. No frozen statement changes or owner ruling are needed;
the brief explicitly permits a better form with justification in this handoff.

There are no other new suspected source errata or unresolved obligations.
The general absorption result even allows arbitrary real `θ`; only the gap
must be positive. Source-specific statements retain `η>0`. Dimension
assumptions for the arithmetic are weakened to `d≥1` (the campaign has
`d≥3`). G7 also works for signed Schwartz profiles; G6 uses the source's
nonnegativity premise. The probability exponent is written as
`(⌊(log L)^(40d)⌋₊ : ℝ)^(40d)`, equal to the real cast of the natural
Wave B expression. No Wave B definitions are copied or imported.

## Exact final verification

All compiles used one targeted invocation at a time through `wt-throttled`.
After merging main:

```
nice -n 5 lake build WaveTurbulence.Foundations.MainGlue.SealInputs
Build completed successfully (9109 jobs).
```

This covers all ten owned modules and finishes without warnings.

```
nice -n 5 lake env lean /home/scott/wt-scratch/main-glue/Axioms.lean
```

Each of the following printed exactly `[propext, Classical.choice, Quot.sound]`:

- `hasLaw_stdComplexGaussian`
- `summable_schwartz_lattice`, `schwartz_lattice_sum_le`
- `integral_gaussian_mass_restrict_le`, `integral_initial_mass_restrict_le`, `initial_mass_event_bound`
- `ceiling_subdivision`, `log_pow_le_final_exponent`, `eventually_final_exponent`
- `eventually_absorb`, `induction_error_absorption_final`
- `measurableSet_smoothDataSet`
- `measurable_fourierEnergyObservable`, `exists_measurable_fourier_energy`

Other checks:

```
python3 /home/scott/.codex/skills/lean-project-architecture/scripts/check_lean_modules.py --root /home/scott/WaveTurbulence-worktrees/cumul
check_lean_modules: PASS (413 Lean files, 0 comparator configurations)

python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json
FROZEN-ANCHOR GUARD OK

git diff main --check
(no output, exit 0)
```

The source scan found no placeholders, custom axioms, unsafe/opaque code,
budget overrides, or quarantined imports in the owned Lean files. No frozen
file, provider, root import, campaign ledger, dependency artifact or toolchain
was edited. No full-library build, Mathlib rebuild, or clean was run.

G4, G8, G9 and G11 remain outside this packet as requested; none is assumed
by or disguised inside these results.

READY main-glue

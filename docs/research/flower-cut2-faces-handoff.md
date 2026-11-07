# C2-D: exact mixed face/BV formula

Packet CX-C2D, 2026-11-06. All files are under this directory. Import
`Cut2D.FixedBox` with this directory's `build/` on `LEAN_PATH` to obtain every export.
Namespace: `WaveTurbulence.Cut2D`.

The packet proves two complementary statements: mixed integration by parts for an
arbitrary smooth amplitude on a box, and an exact finite face formula for the
possibly discontinuous cap/floor amplitude in NOTES §4.1–4.4. The latter is proved
directly from time-domain faces, without smoothing the amplitude or assuming a
formula for its derivative. Each marked clock contributes one inverse angular
frequency. All endpoint phases and orientations remain in the identities.

## C2-D EXPORT

### Objects and conventions

`phase freq t = Complex.exp ((freq * t : ℝ) * Complex.I)` and
`rate freq = (freq : ℂ) * Complex.I`. `boxPhase freq t` is the product of these
phases. All clock integrals use actual Lebesgue measure; the unmarked measure `μ`
is an explicit parameter. `oscIntegral a b freq f` is the integral of
`boxPhase freq * f` on the closed coordinate box `Icc a b`.

For the smooth formula, `face t f x = f (Fin.cons t x)` and
`dface t f x = deriv (fun s => f (Fin.cons s x)) t`.
`mixedBoundary` recursively takes upper endpoint minus lower endpoint minus the
integral of the differentiated amplitude. It enumerates all `3^n` choices, with
retained phases. `mixedMass` replaces each of these terms by its extended norm
and integrates the derivative mass. Thus it includes every mixed derivative and
every complementary endpoint trace, not merely the full interior derivative.
Its definition is in `src/Cut2D/Mixed.lean:23`.

For the time-domain formula, each `ClockBounds` has four lower and two upper
candidates. Its interval is the strict intersection of all six inequalities.
`lo` is their lower maximum; `hi` is their upper minimum.

| Face label | Candidate | Orientation | Intended source role |
|---|---|---|---|
| `Sum.inr 0` | `lower 0` | −1 | fixed lower endpoint |
| `Sum.inr j.succ`, `j : Fin 3` | `lower j.succ` | −1 | ordered child port |
| `Sum.inl 0` | `upper 0` | +1 | fixed upper endpoint |
| `Sum.inl 1` | `upper 1` | +1 | current parent of the tagged stub |

An absent child can duplicate the fixed lower endpoint; an absent parent can
duplicate the fixed upper endpoint. Fixed neighbors can instead supply their
actual fixed clocks. First-index tie breaking chooses one lower maximum and one
upper minimum, preferring a fixed endpoint when it ties a neighbor. Empty or
zero-width intervals activate no faces. These conventions are proved in the
interval/face identities, not assumed in a caller hypothesis.

`FaceLabel = Fin 2 ⊕ Fin 4`; `faceLabel_card n` proves that there are `6^n`
possible mixed labels. For a label vector `s`,

```
facePoint (B x) s i = endpoint (B x i) (s i)
restrictClocks B s x = (x, facePoint (B x) s)
faceTerm (B x) freq s =
  if ∀ i, active (B x i) (s i)
  then (∏ i, orientation (s i)) * boxPhase freq (facePoint (B x) s)
  else 0
faceIntegral μ H B freq s = ∫ x, H x * faceTerm (B x) freq s ∂μ
```

These are explicit face restrictions, not integrals of an equality set against
the old full-dimensional measure. In particular a parent face retains the
marked phase at the parent's clock, and `H` still contains that parent's phase.

The amplitude is the actual unmarked integral

```
capKernel H B x t = (capFloorDomain (B x)).indicator (fun _ => H x) t
marginal μ H B t = ∫ x, capKernel H B x t ∂μ
```

`H` is an arbitrary complex integrable density, with no marked-clock dependence.
All marked-clock dependence of this amplitude is in the cap/floor indicators,
exactly as in NOTES §4.1 after the selected phases have been extracted.

`faceFunctional μ H B s φ` replaces `boxPhase` in the displayed face integral
by a measurable test function `φ`. `faceVariation μ H B s` is the supremum of
its extended norm over all measurable `φ` with `∀ t, ‖φ t‖ ≤ 1`. This is the
bounded-test variation of the explicit signed boundary pushforward. It preserves
cancellation in `H` and between points with the same restricted marked clocks.
`integrable_testFaceTerm` proves that all these tests are integrable under the
stated measurability and L¹ assumptions. `faceVariation_lt_top` and
`sum_faceVariation_lt_top` prove finiteness, with the bound
`faceVariation μ H B s ≤ ∫⁻ x, ‖H x‖ₑ ∂μ`.

### Exact theorem signatures

The following signatures are copied from the compiled sources. The ambient
context is `{X : Type*} [MeasurableSpace X]`; `open MeasureTheory Set` and
`open scoped ContDiff ENNReal`. In this Mathlib, `∞` means C∞, not analytic.

`src/Cut2D/Scalar.lean`:

```lean
theorem scalar_ibp {f f' : ℝ → ℂ} {a b freq : ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume a b) :
    rate freq * (∫ t in a..b, phase freq t * f t) =
      phase freq b * f b - phase freq a * f a - ∫ t in a..b, phase freq t * f' t
```

`src/Cut2D/Mixed.lean`:

```lean
theorem mixed_ibp : ∀ (n : ℕ) (a b freq : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ),
    (∀ i, a i ≤ b i) → (∀ i, freq i ≠ 0) → ContDiff ℝ ∞ f →
    oscIntegral a b freq f = (∏ i, rate (freq i))⁻¹ * mixedBoundary n a b freq f
```

`src/Cut2D/Bounds.lean`:

```lean
theorem mixed_ibp_enorm {n : ℕ} (a b freq : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ)
    (hab : ∀ i, a i ≤ b i) (hfreq : ∀ i, freq i ≠ 0) (hf : ContDiff ℝ ∞ f) :
    ‖oscIntegral a b freq f‖ₑ ≤ ENNReal.ofReal ((∏ i, |freq i|)⁻¹) * mixedMass n a b f
```

`src/Cut2D/Bounds.lean`:

```lean
theorem mixed_ibp_norm {n : ℕ} (a b freq : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ)
    (hab : ∀ i, a i ≤ b i) (hfreq : ∀ i, freq i ≠ 0) (hf : ContDiff ℝ ∞ f)
    {B : ℝ} (hB : 0 ≤ B) (hmass : mixedMass n a b f ≤ ENNReal.ofReal B) :
    ‖oscIntegral a b freq f‖ ≤ (∏ i, |freq i|)⁻¹ * B
```

`src/Cut2D/Caps.lean`:

```lean
theorem capFloor_faces {n : ℕ} (B : Fin n → ClockBounds) (freq : Fin n → ℝ)
    (hfreq : ∀ i, freq i ≠ 0) :
    (∫ t in capFloorDomain B, boxPhase freq t) =
      (∏ i, rate (freq i))⁻¹ * ∑ s : Fin n → FaceLabel, faceTerm B freq s
```

`src/Cut2D/Faces.lean`:

```lean
theorem constrainedIntegral_bound {n : ℕ} {μ : Measure X} {H : X → ℂ} (hH : Integrable H μ)
    (B : X → Fin n → ClockBounds)
    (hl : ∀ i j, Measurable (fun x => (B x i).lower j))
    (hu : ∀ i j, Measurable (fun x => (B x i).upper j)) (freq : Fin n → ℝ)
    (hfreq : ∀ i, freq i ≠ 0) :
    ‖constrainedIntegral μ H B freq‖ ≤ (∏ i, |freq i|)⁻¹ *
      ∑ s : Fin n → FaceLabel, ‖faceIntegral μ H B freq s‖
```

`src/Cut2D/Regularity.lean`:

```lean
theorem marginal_faces_fixedBox {n : ℕ} {μ : Measure X} [SigmaFinite μ] {H : X → ℂ}
    (hH : Integrable H μ) (B : X → Fin n → ClockBounds)
    (hl : ∀ i j, Measurable (fun x => (B x i).lower j))
    (hu : ∀ i j, Measurable (fun x => (B x i).upper j)) (freq : Fin n → ℝ)
    (hfreq : ∀ i, freq i ≠ 0) (a b : Fin n → ℝ)
    (ha : ∀ x i, a i ≤ (B x i).lower 0) (hb : ∀ x i, (B x i).upper 0 ≤ b i) :
    (∫ t, boxPhase freq t * marginal μ H B t) =
      (∏ i, rate (freq i))⁻¹ * ∑ s : Fin n → FaceLabel, faceIntegral μ H B freq s
```

`src/Cut2D/Regularity.lean`:

```lean
theorem marginal_variation_fixedBox {n : ℕ} {μ : Measure X} [SigmaFinite μ] {H : X → ℂ}
    (hH : Integrable H μ) (B : X → Fin n → ClockBounds)
    (hl : ∀ i j, Measurable (fun x => (B x i).lower j))
    (hu : ∀ i j, Measurable (fun x => (B x i).upper j)) (freq : Fin n → ℝ)
    (hfreq : ∀ i, freq i ≠ 0) (a b : Fin n → ℝ)
    (ha : ∀ x i, a i ≤ (B x i).lower 0) (hb : ∀ x i, (B x i).upper 0 ≤ b i) :
    ‖∫ t, boxPhase freq t * marginal μ H B t‖ₑ ≤
      ENNReal.ofReal ((∏ i, |freq i|)⁻¹) * ∑ s : Fin n → FaceLabel, faceVariation μ H B s
```

`src/Cut2D/Gain.lean`:

```lean
theorem marginal_annular_fixedBox {n : ℕ} {μ : Measure X} [SigmaFinite μ] {H : X → ℂ}
    (hH : Integrable H μ) (B : X → Fin n → ClockBounds)
    (hl : ∀ i j, Measurable (fun x => (B x i).lower j))
    (hu : ∀ i j, Measurable (fun x => (B x i).upper j))
    (a b : Fin n → ℝ) (ha : ∀ x i, a i ≤ (B x i).lower 0)
    (hb : ∀ x i, (B x i).upper 0 ≤ b i)
    (sgn resonance : Fin n → ℝ) {scale M : ℝ}
    (hsign : ∀ i, |sgn i| = 1) (hscale : 0 < scale) (hM : 0 < M)
    (hres : ∀ i, M / 4 ≤ |resonance i|) :
    ‖∫ t, boxPhase (fun i => sgn i * scale * resonance i) t * marginal μ H B t‖ₑ ≤
      ENNReal.ofReal ((4 / (scale * M)) ^ n) * ∑ s : Fin n → FaceLabel, faceVariation μ H B s
```

`src/Cut2D/FixedBox.lean`:

```lean
theorem oscIntegral_marginal_eq_integral {n : ℕ} (μ : Measure X) (H : X → ℂ)
    (B : X → Fin n → ClockBounds) (a b freq : Fin n → ℝ)
    (ha : ∀ x i, a i ≤ (B x i).lower 0) (hb : ∀ x i, (B x i).upper 0 ≤ b i) :
    oscIntegral a b freq (marginal μ H B) = ∫ t, boxPhase freq t * marginal μ H B t
```

For the source specialization take `n = 2*P`, constant outer endpoints `a i = s`
and `b i = t`, and `scale = π * δ * L^(2*γ)` with the intended real power.
`annular_inverse_frequency` proves

```
(∏ i, |sgn i * scale * resonance i|)⁻¹ ≤ (4 / (scale * M))^n
```

from `|sgn i| = 1`, `scale > 0`, `M > 0`, and `M/4 ≤ |resonance i|`.
The factor `δ L^(2γ)` is retained. This theorem applies only on nonzero annular
support; it makes no claim of an integration-by-parts gain for `j₂ = 0`.

### Why the nonsmooth theorem is an exact face formula

Fix the unmarked variables `x`. The selected clock domain is a product of
intervals because there is one mark per original tree. Integrate each phase on
its actual interval. The scalar fundamental theorem gives the signed endpoint
difference divided by `i*freq`. Expand the finite product of endpoint sums;
`capFloor_faces` is the resulting pointwise identity. Measurability and the
bound `‖faceTerm‖ ≤ 1` justify integration of the finite sum against `H`.
Fubini then moves the selected clocks outside, producing precisely `marginal`.

For uniform finite outer endpoints, `integrable_jointKernel` proves the needed
joint integrability from `H ∈ L¹` and measurable candidates. Thus the fixed-box
exports have no separate Fubini or derivative-identity premise.
`marginal_eq_zero_outside` proves the zero extension, and
`oscIntegral_marginal_eq_integral` identifies the whole-space formulation with
the literal integral on the prescribed product of intervals.

The general exports `marginal_faces` and `marginal_variation` allow nonuniform,
unbounded candidate functions when the caller supplies joint integrability.
They are additional helpers; the fixed-box exports do not require that premise.

## C2-C and C2-E interface

C2-C must identify its marked original-tree index set with `Fin n`, extract the
constant marked frequencies after fixing momentum labels, and provide the
remaining density `H`, its measure, and the six candidate clocks. In particular,
`upper 1` must be the CURRENT parent clock of the R64 tagged stub, not a frozen
node address. Child candidates follow the ordered anchor ports. Include all
constraints not involving a marked clock in `H` or the unmarked measure.

The theorem's `B` is an arbitrary measurable function of unmarked variables;
there is no fixed-address, fixed-depth, or twist-avoidance hypothesis. Each mixed
label selects only one candidate per original marked tree. A selected child or
parent face can therefore add at most one neighbor pin to that tree; endpoint
roles add none. Connecting those restrictions to the actual R64 excision/gluing
carrier, including merging coincident tags, remains C2-C's construction. No
Lean theorem about a garden carrier is claimed in this analytic packet.

C2-E can bound the complex `faceIntegral` before taking its norm, using
`constrainedIntegral_bound`, or bound its pushforward variation using
`marginal_variation_fixedBox`. No bound on an individual garden shape, no
premise containing the desired M₂ decay, and no `L^(cN)` loss is introduced here.
The coarse L¹ bound on face variation establishes finiteness; it is not proposed
as a substitute for the coherent-family estimates in C2-E.

## Scope and deviations

The smooth theorem assumes global C∞ regularity, a convenient sufficient
condition ensuring all face derivatives and compact Fubini operations exist.
It does not claim minimal Sobolev regularity. The nonsmooth theorem instead
covers the exact cap/floor marginal class above with only measurable candidates
and an L¹ density. It does not assert a Stieltjes theorem for every arbitrary
function satisfying Mathlib's `BoundedVariationOn`, nor an identification of
`faceVariation` with a particular Mathlib vector-measure total-variation object.
The explicit bounded-test mass and its finiteness are the proved BV interface.
This implements NOTES §4.4's direct time-domain-face route.

No new source erratum was found. The R64 indexing repair is respected at the
analytic interface; the combinatorial instantiation is deliberately left to
its assigned packets. This completes C2-D, not C2-C, C2-E, or the flower bound.

## Files and dependencies

| File under `src/Cut2D/` | Content |
|---|---|
| `Scalar.lean` | complex phase, scalar IBP, both endpoints, scalar bound |
| `Box.lean` | explicit restrictions, product Lebesgue Fubini, smooth slices |
| `Mixed.lean` | full recursive mixed identity and mixed mass definition |
| `Bounds.lean` | full face/variation estimate and frequency scaling |
| `Caps.lean` | six roles, tie/empty-interval rules, exact constrained-box identity |
| `Faces.lean` | integrated complex faces and bounded-test variation |
| `Amplitude.lean` | marked clocks outside, nonsmooth marginal identity |
| `Regularity.lean` | measurable joint domain, automatic fixed-box integrability |
| `Gain.lean` | annular inverse-frequency product and marginal estimate |
| `Variation.lean` | integrable boundary tests and finite total face mass |
| `FixedBox.lean` | support and literal fixed-box bridge; imports all exports |

The only direct project imports are
`WaveTurbulence.Foundations.Analysis.CubeSobolev` and
`WaveTurbulence.Foundations.Fourier.SmoothIntervalIntegral`; their smooth
coordinate/parametric-integral lemmas provide the required infrastructure.
The core integration-by-parts and finite-product integral results are Mathlib's.
There is no need to import a WaveB provider or assume a Sumint adapter theorem.

## Checks and axioms

All eleven library modules compile serially through `nice -n 5 lake env lean`
in `/home/scott/WaveTurbulence-dev`, with `LEAN_PATH` pointing at this packet's
`build/`. For each module `NAME`, the exact compilation command was:

```sh
cd /home/scott/WaveTurbulence-dev
LEAN_PATH=/home/scott/wt-scratch/research-cut2/c2d/build nice -n 5 lake env lean \
  --root=/home/scott/wt-scratch/research-cut2/c2d/src \
  -o /home/scott/wt-scratch/research-cut2/c2d/build/Cut2D/NAME.olean \
  /home/scott/wt-scratch/research-cut2/c2d/src/Cut2D/NAME.lean \
  > /home/scott/wt-scratch/research-cut2/c2d/build/NAME.log 2>&1
```

`checks/Audit.lean` imports the full export module and checks zero marks, an
empty interval, tied endpoint candidates counted once, the two-mark role count,
and evaluation at the selected parent clock. It also prints axioms for eighteen
principal results. Its command uses the same environment and `nice` prefix,
with `lake env lean .../c2d/checks/Audit.lean`, logging to `build/Audit.log`.
All final checks exit 0. Final logs have no Lean errors or warnings; the only
extra output is the existing `wt-throttled` toolchain-override notice.

Every printed theorem has exactly these standard axioms:

```
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, new axiom, provider assumption, unsafe declaration, or
heartbeat/recursion/synthesis override. `check.sh` reproduces the serial build
and audit; it does not rebuild dependencies. Validation used the project's
Lean 4.35.0 environment. The main workspace HEAD observed at validation was
`4d145f6fd52e9e26525c9cf3aa159b6544e0afff`. Source and dependency hashes are in
`SOURCE-SHA256.txt`. All writes for this packet stayed inside `c2d/`.

READY cx-c2d

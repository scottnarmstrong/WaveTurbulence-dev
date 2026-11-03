/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.HausdorffYoung
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

/-!
# The Fourier transform on all of `Lᵖ`, `1 ≤ p ≤ 2`

TARGET L2370. The norm-one integral estimate extends the Schwartz Fourier
transform uniquely to an operator `Lᵖ → L^{p'}`. This supplies the full
function-space statement, including inputs without an ordinary `L¹`
Fourier integral. Its value on every Schwartz function is proved explicitly.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

private noncomputable def schwartzFourierLpMap (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    𝓢(V, ℂ) →ₗ[ℂ] Lp (α := V) ℂ q (volume : Measure V) :=
  (SchwartzMap.toLpCLM ℂ ℂ q (volume : Measure V)).toLinearMap.comp
    (FourierTransform.fourierₗ ℂ 𝓢(V, ℂ))

private theorem schwartzFourierLpMap_apply (q : ℝ≥0∞) [Fact (1 ≤ q)] (φ : 𝓢(V, ℂ)) :
    schwartzFourierLpMap q φ = (𝓕 φ).toLp q (volume : Measure V) := rfl

private theorem schwartzToLp_dense (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (fun φ : 𝓢(V, ℂ) => φ.toLp p (volume : Measure V)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
    (μ := (volume : Measure V)) (p := p) hp
  change DenseRange (fun φ : 𝓢(V, ℂ) => φ.toLp p volume) at h
  exact h

/-- Existence of the norm-one Fourier extension from the dense Schwartz class. -/
theorem exists_hausdorffYoungLp (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p))] :
    ∃ T : Lp (α := V) ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
        Lp (α := V) ℂ (ENNReal.conjExponent (ENNReal.ofReal p)) (volume : Measure V),
      (∀ φ : 𝓢(V, ℂ), T (φ.toLp (ENNReal.ofReal p) volume) =
        (𝓕 φ).toLp (ENNReal.conjExponent (ENNReal.ofReal p)) volume) ∧
      (∀ u, ‖T u‖ ≤ ‖u‖) := by
  let e := (SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal p) (volume : Measure V)).toLinearMap
  let f := schwartzFourierLpMap (V := V) (ENNReal.conjExponent (ENNReal.ofReal p))
  have hd : DenseRange e := schwartzToLp_dense (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have hn (φ : 𝓢(V, ℂ)) : ‖f φ‖ ≤ 1 * ‖e φ‖ := by
    change ‖(𝓕 φ).toLp (ENNReal.conjExponent (ENNReal.ofReal p)) volume‖ ≤
      1 * ‖φ.toLp (ENNReal.ofReal p) volume‖
    rw [one_mul, SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
    apply ENNReal.toReal_mono (φ.memLp (ENNReal.ofReal p) volume).eLpNorm_ne_top
    simpa only [SchwartzMap.fourier_coe] using
      integral_fourier_hausdorffYoung_conj hp1 hp2 φ.integrable (φ.memLp (ENNReal.ofReal p) volume)
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · intro φ
    change f.extendOfNorm e (e φ) = f φ
    exact LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ φ
  · intro u
    simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le hd 1 hn u

/-- TARGET L2370: the Fourier transform as a norm-one operator on all of `Lᵖ`.
The `Fact` parameters are the usual typing data for Banach `Lp` spaces. -/
@[expose] noncomputable def hausdorffYoungLp (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p))] :
    Lp (α := V) ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
      Lp (α := V) ℂ (ENNReal.conjExponent (ENNReal.ofReal p)) (volume : Measure V) :=
  Classical.choose (exists_hausdorffYoungLp (V := V) p hp1 hp2)

/-- The `Lp` Fourier extension agrees with the ordinary transform on Schwartz functions. -/
theorem hausdorffYoungLp_apply_schwartz (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p))] (φ : 𝓢(V, ℂ)) :
    hausdorffYoungLp p hp1 hp2 (φ.toLp (ENNReal.ofReal p) volume) =
      (𝓕 φ).toLp (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
  (Classical.choose_spec (exists_hausdorffYoungLp (V := V) p hp1 hp2)).1 φ

/-- The full `Lᵖ → L^{p'}` Hausdorff–Young inequality, with constant one. -/
theorem hausdorffYoungLp_norm_le (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p))]
    (u : Lp (α := V) ℂ (ENNReal.ofReal p) (volume : Measure V)) :
    ‖hausdorffYoungLp p hp1 hp2 u‖ ≤ ‖u‖ :=
  (Classical.choose_spec (exists_hausdorffYoungLp (V := V) p hp1 hp2)).2 u

/-- Agreement with Fourier on the dense Schwartz class uniquely determines the extension. -/
theorem hausdorffYoungLp_unique (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.conjExponent (ENNReal.ofReal p))]
    (T : Lp (α := V) ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
      Lp (α := V) ℂ (ENNReal.conjExponent (ENNReal.ofReal p)) (volume : Measure V))
    (hT : ∀ φ : 𝓢(V, ℂ), T (φ.toLp (ENNReal.ofReal p) volume) =
      (𝓕 φ).toLp (ENNReal.conjExponent (ENNReal.ofReal p)) volume) :
    T = hausdorffYoungLp p hp1 hp2 := by
  apply ContinuousLinearMap.ext
  intro u
  exact (schwartzToLp_dense (V := V) (ENNReal.ofReal p) ENNReal.ofReal_ne_top).induction_on u
    (isClosed_eq T.continuous (hausdorffYoungLp p hp1 hp2).continuous)
    (fun φ => (hT φ).trans (hausdorffYoungLp_apply_schwartz p hp1 hp2 φ).symm)

end WaveTurbulence.Fourier

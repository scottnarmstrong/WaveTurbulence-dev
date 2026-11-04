/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.InvariantProductBounds
public import WaveTurbulence.Foundations.Incoh.SmoothOrdering
public import WaveTurbulence.Foundations.Incoh.LocalizedInterval
public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral

/-!
# Literal causal phase kernels with bounds on every selected clock

`m=0` gives two selected clocks and `m=2` gives four. All interval bounds
are retained, including the outer root and lone-parent layer bounds.
The strict ordering weight enforces causality also for reversed external clocks.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- The literal half-open interval localized by the fixed smooth cutoff. -/
@[expose] def hardLocalizedInterval (χ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  χ x * (Ioc a b).indicator (fun _ => (1 : ℝ)) x

/-- The smooth amplitude retains all selected-clock bounds and the causal ordering. -/
@[expose] def smoothCausalBoxAmplitude (m : ℕ) (χ : ℝ → ℝ) (ε : ℝ)
    (phase a b : Fin (m + 2) → ℝ) : (Fin (m + 2) → ℝ) → ℂ :=
  invariantProductAmplitude (fun j => localizedInterval χ ε (a j) (b j)) phase
    (smoothOrderingWeight (m + 1) ε)

/-- The exact hard-boundary amplitude. -/
@[expose] def causalBoxAmplitude (m : ℕ) (χ : ℝ → ℝ)
    (phase a b : Fin (m + 2) → ℝ) : (Fin (m + 2) → ℝ) → ℂ :=
  invariantProductAmplitude (fun j => hardLocalizedInterval χ (a j) (b j)) phase
    (strictOrderingWeight (m + 1))

/-- The canonical smooth approximation of the actual causal time integral. -/
@[expose] def smoothCausalBoxKernel (m : ℕ) (χ : ℝ → ℝ) (ε : ℝ)
    (phase a b : Fin (m + 2) → ℝ) : (Fin 2 → ℝ) → ℂ :=
  Fourier.weightedOrderedIntegral (m + 2) χ χ (smoothCausalBoxAmplitude m χ ε phase a b)

/-- The literal causal phase/time-box integral, including every selected layer interval. -/
@[expose] def causalBoxKernel (m : ℕ) (χ : ℝ → ℝ)
    (phase a b : Fin (m + 2) → ℝ) : (Fin 2 → ℝ) → ℂ :=
  Fourier.weightedOrderedIntegral (m + 2) χ χ (causalBoxAmplitude m χ phase a b)

@[fun_prop] theorem contDiff_smoothCausalBoxAmplitude (m : ℕ) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (ε : ℝ) (phase a b : Fin (m + 2) → ℝ) :
    ContDiff ℝ ∞ (smoothCausalBoxAmplitude m χ ε phase a b) :=
  contDiff_invariantProductAmplitude (fun j => contDiff_localizedInterval hχ ε (a j) (b j)) phase
    (contDiff_smoothOrderingWeight (m + 1) ε)

/-- The fixed cutoff gives a uniform time bound, independently of all phases and endpoints. -/
theorem norm_smoothCausalBoxAmplitude_le (m : ℕ) {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    {ε : ℝ} (hε : 0 < ε) (phase a b : Fin (m + 2) → ℝ) (hab : a ≤ b) (v : Fin (m + 2) → ℝ) :
    ‖smoothCausalBoxAmplitude m χ ε phase a b v‖ ≤ h.bound ^ (m + 2) := by
  apply (norm_invariantProductAmplitude_le _ phase (norm_smoothOrderingWeight_le (m + 1) ε) v).trans
  apply norm_coordinateFactorProduct_le
  intro j x
  exact (norm_localizedInterval_le hε (hab j) x).trans (by simpa only [Real.norm_eq_abs] using h.abs_le x)

/-- The smooth amplitudes converge at every internal clock tuple. -/
theorem tendsto_smoothCausalBoxAmplitude (m : ℕ) (χ : ℝ → ℝ) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (phase a b : Fin (m + 2) → ℝ)
    (hab : a ≤ b) (v : Fin (m + 2) → ℝ) :
    Tendsto (fun n => smoothCausalBoxAmplitude m χ (ε n) phase a b v) atTop
      (𝓝 (causalBoxAmplitude m χ phase a b v)) := by
  have hp : Tendsto (fun n => coordinateFactorProduct (fun j => localizedInterval χ (ε n) (a j) (b j)) v)
      atTop (𝓝 (coordinateFactorProduct (fun j => hardLocalizedInterval χ (a j) (b j)) v)) := by
    apply tendsto_finsetProd
    intro j _
    exact (Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_smoothInterval hε hlim (hab j) (v j)).const_mul (χ (v j)))
  exact (hp.mul tendsto_const_nhds).mul (tendsto_smoothOrderingWeight (m + 1) hε hlim v)

end WaveTurbulence.Incoh

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Time Fourier transform and extended weighted Fourier norms

TARGET L579–L591, `(normX1)` and `(locnorm)`. Time variables use the physical
coordinate space `Fin r → ℝ` with product Lebesgue measure and the usual dot
product pairing. The weight is `max_j sqrt(1 + λ_j²)`, with value one when
there are no time coordinates. Norms take values in `ℝ≥0∞`; a nonintegrable
input has norm infinity, even though Lean's Bochner integral defaults to zero.
Restriction norms are infima over all whole-space extensions.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- The coordinate dot product for the time Fourier transform. -/
@[expose] def timePairing (r : ℕ) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ

/-- TARGET L579: Fourier transform with phase `exp(-2πi λ·t)`. -/
@[expose] noncomputable def timeFourier {r : ℕ}
    (f : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (timePairing r) f

/-- The largest Japanese bracket of the time frequencies. The zero-dimensional
convention is one, so that every real power is meaningful. -/
@[expose] noncomputable def timeBracket {r : ℕ} (ξ : Fin r → ℝ) : ℝ :=
  1 + (Finset.univ.sup' (Finset.univ_nonempty) fun i : Option (Fin r) =>
    match i with
    | none => 0
    | some j => Real.sqrt (1 + ξ j ^ 2) - 1)

/-- The weight in TARGET `(normX1)`; `θ` may be negative. -/
@[expose] noncomputable def timeWeight {r : ℕ} (θ : ℝ) (ξ : Fin r → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (timeBracket ξ ^ θ)

/-- TARGET `(normX1)`, with the no-junk convention of WAVE-B §2.6. -/
@[expose] noncomputable def timeFourierNorm {r : ℕ} (θ : ℝ)
    (f : (Fin r → ℝ) → ℂ) : ℝ≥0∞ := by
  classical
  exact if Integrable f then ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier f ξ‖ₑ else ⊤

/-- TARGET `(locnorm)`: infimum over extensions agreeing at every point of
`B`. An empty family of extensions has value infinity. -/
@[expose] noncomputable def timeRestrictionNorm {r : ℕ} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (f : B → ℂ) : ℝ≥0∞ :=
  ⨅ (g : (Fin r → ℝ) → ℂ) (_ : ∀ t : B, g t = f t), timeFourierNorm θ g

@[simp] theorem timeFourier_zero (r : ℕ) :
    timeFourier (r := r) (fun _ => 0) = 0 := by
  ext ξ
  simp [timeFourier, VectorFourier.fourierIntegral]

@[simp] theorem timeFourierNorm_zero (r : ℕ) (θ : ℝ) :
    timeFourierNorm (r := r) θ (fun _ => 0) = 0 := by
  simp [timeFourierNorm]

theorem timeFourierNorm_of_not_integrable {r : ℕ} {θ : ℝ}
    {f : (Fin r → ℝ) → ℂ} (hf : ¬ Integrable f) : timeFourierNorm θ f = ⊤ := by
  simp [timeFourierNorm, hf]

theorem timeFourierNorm_eq_lintegral {r : ℕ} {θ : ℝ}
    {f : (Fin r → ℝ) → ℂ} (hf : Integrable f) :
    timeFourierNorm θ f = ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier f ξ‖ₑ := by
  simp [timeFourierNorm, hf]

theorem timeRestrictionNorm_le_extension {r : ℕ} {θ : ℝ}
    {B : Set (Fin r → ℝ)} {f : B → ℂ} (g : (Fin r → ℝ) → ℂ)
    (hg : ∀ t : B, g t = f t) : timeRestrictionNorm θ B f ≤ timeFourierNorm θ g :=
  iInf_le_of_le g (iInf_le_of_le hg le_rfl)

theorem timeRestrictionNorm_le {r : ℕ} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → ℂ) :
    timeRestrictionNorm θ B (fun t => f t) ≤ timeFourierNorm θ f :=
  timeRestrictionNorm_le_extension f (fun _ => rfl)

@[simp] theorem timeRestrictionNorm_zero {r : ℕ} (θ : ℝ)
    (B : Set (Fin r → ℝ)) : timeRestrictionNorm θ B (fun _ => 0) = 0 := by
  apply le_antisymm _ bot_le
  exact (timeRestrictionNorm_le θ B (fun _ => 0)).trans (by simp)

/-- Translation changes the Fourier transform by a unit complex phase. -/
theorem timeFourier_translate {r : ℕ} (f : (Fin r → ℝ) → ℂ) (a : Fin r → ℝ) :
    timeFourier (fun t => f (t + a)) =
      fun ξ => Real.fourierChar (timePairing r a ξ) • timeFourier f ξ :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

/-- Invariance of the weighted Fourier norm under time translation. -/
theorem timeFourierNorm_translate {r : ℕ} (θ : ℝ)
    (f : (Fin r → ℝ) → ℂ) (a : Fin r → ℝ) :
    timeFourierNorm θ (fun t => f (t + a)) = timeFourierNorm θ f := by
  have hi : Integrable (fun t => f (t + a)) ↔ Integrable f := by
    constructor
    · intro h
      simpa only [add_assoc, neg_add_cancel, add_zero] using h.comp_add_right (-a)
    · intro h
      exact h.comp_add_right a
  unfold timeFourierNorm
  rw [hi]
  split_ifs
  · rw [timeFourier_translate]
    simp only [Circle.enorm_smul]
  · rfl

end WaveTurbulence.Fourier

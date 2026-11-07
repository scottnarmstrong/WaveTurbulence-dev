/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SelectedCoordinateMarginal
public import WaveTurbulence.Foundations.Fourier.HausdorffYoung

/-!
# Sparse native transforms are ordinary Fourier transforms of marginals

The coordinate split preserves Lebesgue measure. Fourier Fubini is
justified by genuine integrability and the unit-norm character. Thus
the selected one- or two-coordinate amplitude is eligible for the
proved L² endpoint of Hausdorff--Young (Plancherel's bound).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Classical

namespace WaveTurbulence.SumintPar

/-- The exact sparse native Fourier integral is the ordinary Fourier transform of its marginal. -/
theorem selectedCoordinate_integral_eq_timeFourier {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hf : Integrable f)
    (ξ : Fin r → ℝ) :
    (∫ u, selectedCoordinateCharacter v ξ u*f u) =
      Fourier.timeFourier (selectedCoordinateMarginal v hv f) ξ := by
  let e := selectedCoordinateSplit v hv
  let g (z : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ)) := f (e.symm z)
  let k (x : Fin r → ℝ) : ℂ := Real.fourierChar (-Fourier.timePairing r x ξ)
  let G (z : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ)) := g z*k z.1
  have hk : Continuous k := by
    dsimp [k]
    simp_rw [Real.fourierChar_apply]
    unfold Fourier.timePairing
    change Continuous (fun x : Fin r → ℝ => Complex.exp ((2*Real.pi*(-∑ j, x j*ξ j):ℝ)*Complex.I))
    fun_prop
  have hgi : Integrable g := integrable_selectedCoordinateSplit_symm v hv f hf
  have hG : Integrable G := hgi.mul_bdd (hk.comp continuous_fst).aestronglyMeasurable
    (ae_of_all _ (fun _ => (Circle.norm_coe _).le))
  have hGp : Integrable G (volume.prod volume) := by simpa only [← Measure.volume_eq_prod] using hG
  calc
    _ = ∫ u, G (e u) := by
      apply integral_congr_ae
      apply ae_of_all
      intro u
      have hc := selectedCoordinateCharacter_split_symm v hv ξ (e u)
      rw [MeasurableEquiv.symm_apply_apply] at hc
      dsimp only [G,g,k]
      rw [MeasurableEquiv.symm_apply_apply,← hc]
      ring
    _ = ∫ z, G z := (volume_preserving_selectedCoordinateSplit v hv).integral_comp e.measurableEmbedding G
    _ = ∫ x : Fin r → ℝ, ∫ y : {i : ι // i ∉ Set.range v} → ℝ, G (x,y) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod G hGp
    _ = _ := by
      change (∫ x : Fin r → ℝ, ∫ y : {i : ι // i ∉ Set.range v} → ℝ, g (x,y)*k x) =
        ∫ x : Fin r → ℝ, Real.fourierChar (-Fourier.timePairing r x ξ) • selectedCoordinateMarginal v hv f x
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change (∫ y : {i : ι // i ∉ Set.range v} → ℝ, g (x,y)*k x) =
        Real.fourierChar (-Fourier.timePairing r x ξ) • selectedCoordinateMarginal v hv f x
      rw [integral_mul_const]
      dsimp only [g,k,selectedCoordinateMarginal]
      rw [Circle.smul_def,smul_eq_mul,mul_comm]

/-- The L² Fourier bound applies directly to a selected-coordinate marginal. -/
theorem eLpNorm_timeFourier_selectedMarginal_le {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hf : Integrable f)
    (hf2 : MemLp (selectedCoordinateMarginal v hv f) 2) :
    eLpNorm (Fourier.timeFourier (selectedCoordinateMarginal v hv f)) 2 ≤
      eLpNorm (selectedCoordinateMarginal v hv f) 2 := by
  have hy := Fourier.timeFourier_hausdorffYoung (by norm_num : (1:ℝ) ≤ 2) (le_refl (2:ℝ))
    (integrable_selectedCoordinateMarginal v hv f hf) (by simpa using hf2)
  have hc : ENNReal.HolderConjugate (2:ℝ≥0∞) 2 := by
    simpa only [ENNReal.ofReal_ofNat] using Real.HolderConjugate.two_two.ennrealOfReal
  have he : ENNReal.conjExponent (2:ℝ≥0∞) = 2 := hc.conjExponent_eq
  simpa only [ENNReal.ofReal_ofNat,he] using hy

end WaveTurbulence.SumintPar

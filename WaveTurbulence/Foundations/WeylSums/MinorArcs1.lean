/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearGlobal
public import WaveTurbulence.Foundations.WeylSums.CoordinateDerivativeBounds

/-! # DH23 Lemma 6.6(1): the global minor-arc estimate -/

public section
open MeasureTheory Set
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- DH23 `NTlem21`, with finite coordinate derivative bounds, arbitrary
joint amplitudes, and time support `|s|<L^(2γ)`. The result is valid for every
width at least one, without the source's auxiliary logarithmic restriction. -/
theorem dh23_minor1_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ L width : ℝ, 2 ≤ L → 1 ≤ width →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ),
      (∀ x y, Measurable (fun s => Φ s x y)) →
      (∀ s, ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s))) →
      (∀ s, L^(2*γ) ≤ |s| → ∀ x y, Φ s x y = 0) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ s, CoordinateDerivativeBound (10*d) (packedBilinearAmplitude (Φ s)) D) →
      ∀ a b ξ ζ : Mom d,
      Integrable (fun s => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ∧
      (∫ s, ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ≤
        C*D*width^(4*d)*L^(2*(d : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := exists_weighted_bilinear_global_integral_bound d hd
  let J : ℝ := (Fintype.card (Fin d × Fin 2)+1 : ℝ)^(10*d)
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨C*J,mul_pos hC hJ,?_⟩
  intro γ hγ L width hL hw Φ htime hΦ hsupp D hD hcoord a b ξ ζ
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hupper : L^(2*γ) ≤ L^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hγ.2] : 2*γ ≤ 2)
    simpa only [Real.rpow_two] using hh
  have hderiv (s : ℝ) (j : ℕ) (hj : j ≤ 10*d) (x : EuclideanSpace ℝ (Fin d × Fin 2)) :
      ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ J*D :=
    (hcoord s).operator_bound hD j hj x
  have hh := hb L width hL hw Φ htime hΦ (J*D) (mul_nonneg hJ.le hD) hderiv a b ξ ζ
  let f := fun s : ℝ => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖
  have heq : {s : ℝ | |s| ≤ L^2}.indicator f = f := by
    funext s
    by_cases hs : |s| ≤ L^2
    · simp [Set.indicator,hs]
    · have hz : weightedBilinearLatticeSum Φ L width s a b ξ ζ = 0 := by
        have hs' : L^(2*γ) ≤ |s| := hupper.trans (le_of_not_ge hs)
        simp [weightedBilinearLatticeSum,hsupp s hs']
      simp [Set.indicator,hs,f,hz]
  have hfi : Integrable f := by
    rw [← heq]
    exact (integrable_indicator_iff (by measurability)).mpr hh.1
  refine ⟨hfi,?_⟩
  have hwhole : (∫ s, f s) = ∫ s in {s : ℝ | |s| ≤ L^2}, f s := by
    rw [← integral_indicator (by measurability),heq]
  change (∫ s, f s) ≤ _
  rw [hwhole]
  exact hh.2.trans_eq (by ring)

end WaveTurbulence.WeylSums

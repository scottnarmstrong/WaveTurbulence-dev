/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylMoments
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetry

/-! # A symmetric global Weyl moment window -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- Symmetry converts the unit-interval moment into a bound on a fixed
symmetric window; both integrability and the quantitative estimate are retained. -/
theorem exists_weyl_symmetric_moment_bound (p : ℝ) (hp : 4 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      IntegrableOn (fun t => weylSupremum L t^p) {t : ℝ | |t| ≤ 1/2} ∧
      (∫ t in {t : ℝ | |t| ≤ 1/2}, weylSupremum L t^p) ≤ C*L^(p-2) := by
  obtain ⟨C,hC,hb,_⟩ := weyl_moment_bounds p hp
  obtain ⟨C₀,hC₀,hint⟩ := exists_weylSupremum_integral_bound
  refine ⟨2*C,by positivity,?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  let f : ℝ → ℝ := fun t => weylSupremum L t^p
  have hfn (t : ℝ) : 0 ≤ f t := Real.rpow_nonneg (weylSupremum_nonneg hLp t) _
  have hi01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hint L p hL hp).1
  have hiN : IntervalIntegrable f volume (-1) 0 := by
    have hh := (IntervalIntegrable.iff_comp_neg).mp hi01
    simpa only [neg_zero,f,weylSupremum_neg hLp] using hh.symm
  have hiAll : IntegrableOn f (Ioc (-1 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (hiN.trans hi01)
  have hnegInt : (∫ t in (-1 : ℝ)..0, f t) = ∫ t in (0 : ℝ)..1, f t := by
    have hh := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := (1 : ℝ))
    simpa only [neg_zero,f,weylSupremum_neg hLp] using hh.symm
  have hsub : {t : ℝ | |t| ≤ 1/2} ⊆ Ioc (-1 : ℝ) 1 := by
    intro t ht
    change |t| ≤ 1/2 at ht
    obtain ⟨hl,hu⟩ := abs_le.mp ht
    exact ⟨by linarith,by linarith⟩
  refine ⟨hiAll.mono_set hsub,?_⟩
  calc
    _ ≤ ∫ t in Ioc (-1 : ℝ) 1, f t := setIntegral_mono_set hiAll
      (Filter.Eventually.of_forall hfn) (Filter.Eventually.of_forall hsub)
    _ = ∫ t in (-1 : ℝ)..1, f t := (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = (∫ t in (-1 : ℝ)..0, f t)+(∫ t in (0 : ℝ)..1, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hiN hi01).symm
    _ ≤ (2*C)*L^(p-2) := by rw [hnegInt]; have hh := hb L hL; dsimp [f] at *; linarith

end WaveTurbulence.WeylSums

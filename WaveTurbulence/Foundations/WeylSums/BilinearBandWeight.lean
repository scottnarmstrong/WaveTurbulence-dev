/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearGlobal
public import Mathlib.Data.Set.Card

/-! # A nonnegative lattice weight majorizing radius-two momentum balls -/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- The fixed width-four pair cutoff, equal to one on radius-two balls. -/
@[expose] noncomputable def bilinearBandWeight {d : ℕ} (L : ℝ) (a b : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  latticeCutoff ((4 : ℝ)⁻¹ • (latticePoint L q.1-a))*
    latticeCutoff ((4 : ℝ)⁻¹ • (latticePoint L q.2-b))

theorem latticeCutoff_nonneg {d : ℕ} (x : Mom d) : 0 ≤ latticeCutoff x :=
  prod_nonneg (fun _i _hi => Fourier.chi0_nonneg _)

theorem bilinearBandWeight_nonneg {d : ℕ} (L : ℝ) (a b : Mom d) (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    0 ≤ bilinearBandWeight L a b q := mul_nonneg (latticeCutoff_nonneg _) (latticeCutoff_nonneg _)

theorem finite_bilinearBandWeight {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d) :
    (Function.support (bilinearBandWeight L a b)).Finite := by
  have hLp : 0 < L*4 := by positivity
  apply ((finite_latticeCutoff hLp ((4 : ℝ)⁻¹ • a)).prod
    (finite_latticeCutoff hLp ((4 : ℝ)⁻¹ • b))).subset
  intro q hq
  change latticeCutoff _ ≠ 0 ∧ latticeCutoff _ ≠ 0
  simpa only [Function.mem_support,bilinearBandWeight,
    scaled_latticePoint_sub hL.ne' (by norm_num : (4 : ℝ) ≠ 0),mul_ne_zero_iff] using hq

/-- Coordinate projections do not increase Euclidean norm, so the plateau
of the width-four cutoff contains the entire radius-two ball. -/
theorem latticeCutoff_quarter_eq_one {d : ℕ} (x : Mom d) (hx : ‖x‖ ≤ 2) :
    latticeCutoff ((4 : ℝ)⁻¹ • x) = 1 := by
  apply prod_eq_one
  intro i hi
  apply Fourier.chi0_eq_one
  have hh : |x i| ≤ 2 := by
    have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    exact hcoord.trans hx
  change |(4 : ℝ)⁻¹*x i| ≤ 1/2
  rw [abs_mul]
  norm_num
  linarith

theorem bilinearBandWeight_eq_one {d : ℕ} (L : ℝ) (a b : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ))
    (ha : ‖latticePoint L q.1-a‖ ≤ 2) (hb : ‖latticePoint L q.2-b‖ ≤ 2) :
    bilinearBandWeight L a b q = 1 := by
  rw [bilinearBandWeight,latticeCutoff_quarter_eq_one _ ha,latticeCutoff_quarter_eq_one _ hb,one_mul]

/-- The pair cutoff Fourier sum has a uniform square-window `L¹` bound. -/
theorem exists_bilinearBandWeight_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 2 ≤ L → ∀ a b : Mom d,
      IntegrableOn (fun s : ℝ => ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ),
        (bilinearBandWeight L a b q : ℂ)*e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖)
        {s : ℝ | |s| ≤ L^2} ∧
      (∫ s in {s : ℝ | |s| ≤ L^2}, ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ),
        (bilinearBandWeight L a b q : ℂ)*e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖) ≤ C*L^(2*(d : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := exists_weighted_bilinear_global_integral_bound d hd
  refine ⟨C*(4 : ℝ)^(4*d),by positivity,?_⟩
  intro L hL a b
  let Φ : ℝ → Mom d → Mom d → ℂ := fun _ _ _ => 1
  have hpack (s : ℝ) : packedBilinearAmplitude (Φ s) = (fun _ : EuclideanSpace ℝ (Fin d × Fin 2) => (1 : ℂ)) := rfl
  have hcont (s : ℝ) : ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s)) := by rw [hpack s]; exact contDiff_const
  have hderiv (s : ℝ) (j : ℕ) (_hj : j ≤ 10*d) (x : EuclideanSpace ℝ (Fin d × Fin 2)) :
      ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ 1 := by
    rw [hpack s]
    by_cases hj : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      norm_num
    · rw [iteratedFDeriv_const_of_ne hj]
      simp
  have hh := hb L 4 hL (by norm_num) Φ (fun x y => measurable_const) hcont 1 (by norm_num) hderiv a b 0 0
  have heq (s : ℝ) : weightedBilinearLatticeSum Φ L 4 s a b 0 0 =
      ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (bilinearBandWeight L a b q : ℂ)*
        e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2)) := by
    simp only [weightedBilinearLatticeSum,bilinearBandWeight,Φ,mul_one,inner_zero_right,zero_add]
  simpa only [heq,mul_one,mul_assoc] using hh

end WaveTurbulence.WeylSums

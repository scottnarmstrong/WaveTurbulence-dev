/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylTensorFactors
public import WaveTurbulence.Foundations.WeylSums.LatticeBoxes

/-!
# Quantitative Fourier-to-lattice comparison at two scales

The physical lattice scale and the auxiliary cutoff scale are independent.
The Fourier `L¹` constant is explicit, so translation-invariant Fourier
weights give bounds uniform in all real spatial centers.
-/

public section
open Finset MeasureTheory
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- A Fourier representation reduces a compact joint lattice sum to a Weyl
product. This conditional representation lemma is consumed with the proved
Fourier inversion and translation theorems, rather than assumed as a source estimate. -/
theorem norm_lattice_sum_le_of_fourier_representation {m : ℕ}
    (χ F : EuclideanSpace ℝ (Fin m) → ℂ) (hF : Integrable F)
    (hf : ∀ x, χ x = ∫ ξ, F ξ * e (∑ i, ξ i*x i))
    (L M : ℝ) (h : Fin m → ℤ) (hL : 0 < L) (hM : 0 < M)
    (hplateau : ∀ n : Fin m → ℤ,
      χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) ≠ 0 →
        ∀ i, weylCutoff ((n i : ℝ)/M) = 1)
    (s r : Fin m → ℝ) :
    ‖∑' n : Fin m → ℤ,
      χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) *
      e (∑ i, (s i*((n i : ℝ)+h i)^2+r i*((n i : ℝ)+h i)))‖ ≤
        (∫ ξ, ‖F ξ‖) * ∏ i, weylSupremum M (s i) := by
  classical
  have hfinite : (∑' n : Fin m → ℤ,
        χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) *
        e (∑ i, (s i * ((n i : ℝ)+h i)^2 + r i * ((n i : ℝ)+h i)))) =
      ∑ n ∈ latticeBox M m,
        χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) *
        e (∑ i, (s i * ((n i : ℝ)+h i)^2 + r i * ((n i : ℝ)+h i))) := by
    apply tsum_eq_sum
    intro n hn
    have hz : χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) = 0 := by
      by_contra hz
      apply hn
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hout
      have hzero := weylCutoff_eq_zero_of_not_mem hM (n i) hout
      have hone := hplateau n hz i
      exact zero_ne_one (hzero.symm.trans hone)
    rw [hz, zero_mul]
  rw [hfinite, sum_latticeBox]
  let θ (i : Fin m) (n : ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) : ℂ := weylCutoff ((n : ℤ)/M)
  let x (i : Fin m) (n : ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) : ℝ := (((n : ℤ) : ℝ)+h i)/L
  have hrep (v : Fin m → ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) :
      χ (WithLp.toLp 2 (fun i => x i (v i))) =
        (∏ i, θ i (v i)) * (∫ ξ, F ξ * e (∑ i, (ξ i * x i (v i)))) := by
    have heq := hf (WithLp.toLp 2 (fun i => x i (v i)))
    simp only at heq
    rw [← heq]
    by_cases hz : χ (WithLp.toLp 2 (fun i => x i (v i))) = 0
    · simp [hz]
    · have hone : ∀ i, θ i (v i) = 1 := hplateau (fun i => (v i : ℤ)) hz
      simp only [hone, prod_const_one, one_mul]
  have hphase (v : Fin m → ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) :
      (∑ i, (s i * ((((v i : ℤ) : ℝ)+h i))^2 + r i * (((v i : ℤ) : ℝ)+h i))) =
      ∑ i, ((s i * L^2) * (x i (v i))^2 + (r i * L) * x i (v i)) := by
    apply sum_congr rfl
    intro i hi
    dsimp [x]
    field_simp [hL.ne']
  simp_rw [hphase]
  have hrep' (v : Fin m → ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) := hrep v
  dsimp only [x] at hrep'
  simp_rw [hrep']
  have hb (i : Fin m) (ρ : ℝ) :
      ‖∑ n, θ i n * e ((s i * L^2) * (x i n)^2 + ρ * x i n)‖ ≤ weylSupremum M (s i) := by
    have heq (n : ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)) :
        (s i * L^2) * (x i n)^2 + ρ * x i n =
          s i * ((((n : ℤ) : ℝ)+h i))^2 + (ρ/L)*(((n : ℤ) : ℝ)+h i) := by
      dsimp [x]
      field_simp [hL.ne']
    simp_rw [heq]
    rw [sum_coe_sort (Icc (-⌈M⌉ : ℤ) ⌈M⌉)
      (fun n => weylCutoff ((n : ℝ)/M) * e (s i * ((n : ℝ)+h i)^2 + (ρ/L)*((n : ℝ)+h i)))]
    exact norm_shifted_weyl_factor_le hM (s i) (ρ/L) (h i)
  have hh := norm_fourier_tensor_reduction_le F hF θ x
    (fun i => s i * L^2) (fun i => r i * L) (fun i => weylSupremum M (s i))
    (fun i => weylSupremum_nonneg hM _) hb
  exact hh

end WaveTurbulence.WeylSums

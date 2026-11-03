/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylTensorFactors
public import WaveTurbulence.Foundations.WeylSums.LatticeBoxes

/-!
# Standard reduction of compact joint lattice cutoffs to Weyl products

DH23 Lemma 6.6 and TARGET (lemcub3). The joint cutoff need not separate.
Its Fourier transform shifts the coordinate linear frequencies, and the
constant is independent of scale, integer centers, and all phase frequencies.
The plateau premise records the support box in which auxiliary coordinate
cutoffs equal one; `exists_compact_tensor_plateau` supplies such cutoffs for
every compactly supported joint amplitude after a fixed enlargement.
-/

public section
open Finset MeasureTheory
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- Generic standard Weyl reduction, for any smooth compact joint cutoff.
The dimension `m` can be `2d` or `3d`; arbitrary quadratic frequencies cover
both the bilinear and cubic diagonalizations. -/
theorem compact_lattice_weyl_reduction {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (h : Fin m → ℤ), 0 < L →
      (∀ n : Fin m → ℤ,
        χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) ≠ 0 →
          ∀ i, weylCutoff ((n i : ℝ)/L) = 1) →
      ∀ s r : Fin m → ℝ,
      ‖∑' n : Fin m → ℤ,
        χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) *
        e (∑ i, (s i * ((n i : ℝ)+h i)^2 + r i * ((n i : ℝ)+h i)))‖ ≤
          C * ∏ i, weylSupremum L (s i) := by
  obtain ⟨F, hF, hf⟩ := exists_compact_fourier_representation χ hc hs
  have hFn : 0 ≤ ∫ ξ, ‖F ξ‖ := integral_nonneg (fun ξ => norm_nonneg _)
  refine ⟨(∫ ξ, ‖F ξ‖)+1, by linarith, ?_⟩
  intro L h hL hplateau s r
  classical
  have hfinite : (∑' n : Fin m → ℤ,
        χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)) *
        e (∑ i, (s i * ((n i : ℝ)+h i)^2 + r i * ((n i : ℝ)+h i)))) =
      ∑ n ∈ latticeBox L m,
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
      have hzero := weylCutoff_eq_zero_of_not_mem hL (n i) hout
      have hone := hplateau n hz i
      exact zero_ne_one (hzero.symm.trans hone)
    rw [hz, zero_mul]
  rw [hfinite, sum_latticeBox]
  let θ (i : Fin m) (n : ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) : ℂ := weylCutoff ((n : ℤ)/L)
  let x (i : Fin m) (n : ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) : ℝ := (((n : ℤ) : ℝ)+h i)/L
  have hrep (v : Fin m → ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) :
      χ (WithLp.toLp 2 (fun i => x i (v i))) =
        (∏ i, θ i (v i)) * (∫ ξ, F ξ * e (∑ i, (ξ i * x i (v i)))) := by
    have heq := hf (WithLp.toLp 2 (fun i => x i (v i)))
    simp only at heq
    rw [← heq]
    by_cases hz : χ (WithLp.toLp 2 (fun i => x i (v i))) = 0
    · simp [hz]
    · have hone : ∀ i, θ i (v i) = 1 := hplateau (fun i => (v i : ℤ)) hz
      simp only [hone, prod_const_one, one_mul]
  have hphase (v : Fin m → ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) :
      (∑ i, (s i * ((((v i : ℤ) : ℝ)+h i))^2 + r i * (((v i : ℤ) : ℝ)+h i))) =
      ∑ i, ((s i * L^2) * (x i (v i))^2 + (r i * L) * x i (v i)) := by
    apply sum_congr rfl
    intro i hi
    dsimp [x]
    field_simp [hL.ne']
  simp_rw [hphase]
  have hrep' (v : Fin m → ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) := hrep v
  dsimp only [x] at hrep'
  simp_rw [hrep']
  have hb (i : Fin m) (ρ : ℝ) :
      ‖∑ n, θ i n * e ((s i * L^2) * (x i n)^2 + ρ * x i n)‖ ≤ weylSupremum L (s i) := by
    have heq (n : ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) :
        (s i * L^2) * (x i n)^2 + ρ * x i n =
          s i * ((((n : ℤ) : ℝ)+h i))^2 + (ρ/L)*(((n : ℤ) : ℝ)+h i) := by
      dsimp [x]
      field_simp [hL.ne']
    simp_rw [heq]
    rw [sum_coe_sort (Icc (-⌈L⌉ : ℤ) ⌈L⌉)
      (fun n => weylCutoff ((n : ℝ)/L) * e (s i * ((n : ℝ)+h i)^2 + (ρ/L)*((n : ℝ)+h i)))]
    exact norm_shifted_weyl_factor_le hL (s i) (ρ/L) (h i)
  have hh := norm_fourier_tensor_reduction_le F hF θ x
    (fun i => s i * L^2) (fun i => r i * L) (fun i => weylSupremum L (s i))
    (fun i => weylSupremum_nonneg hL _) hb
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith)
    (prod_nonneg (fun i _ => weylSupremum_nonneg hL _)))

end WaveTurbulence.WeylSums

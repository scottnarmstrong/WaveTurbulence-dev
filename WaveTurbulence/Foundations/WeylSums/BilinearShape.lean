/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.TranslatedLatticeBound

/-! # The fixed compact cutoff after bilinear diagonalization -/

public section
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- The fixed joint shape in the sum/difference coordinates. -/
@[expose] noncomputable def bilinearDiagonalCutoff
    (z : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (Fourier.chi0 ((z 0+z 1)/2) * Fourier.chi0 ((z 0-z 1)/2) : ℝ)

/-- Its support lies in the coordinate square of radius two. -/
theorem bilinearDiagonalCutoff_support (z : EuclideanSpace ℝ (Fin 2))
    (hz : bilinearDiagonalCutoff z ≠ 0) (i : Fin 2) : |z i| ≤ 2 := by
  have hu : |(z 0+z 1)/2| < 1 := by
    by_contra hh
    apply hz
    simp only [bilinearDiagonalCutoff, Fourier.chi0_eq_zero (not_lt.mp hh), zero_mul, Complex.ofReal_zero]
  have hv : |(z 0-z 1)/2| < 1 := by
    by_contra hh
    apply hz
    simp only [bilinearDiagonalCutoff, Fourier.chi0_eq_zero (not_lt.mp hh), mul_zero, Complex.ofReal_zero]
  obtain ⟨hul,huu⟩ := abs_lt.mp hu
  obtain ⟨hvl,hvu⟩ := abs_lt.mp hv
  fin_cases i
  · change |z 0| ≤ 2
    apply abs_le.mpr
    constructor <;> linarith only [hul,huu,hvl,hvu]
  · change |z 1| ≤ 2
    apply abs_le.mpr
    constructor <;> linarith only [hul,huu,hvl,hvu]

theorem bilinearDiagonalCutoff_hasCompactSupport : HasCompactSupport bilinearDiagonalCutoff := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4)
  intro z hz
  by_contra hnonzero
  have h0 := bilinearDiagonalCutoff_support z hnonzero 0
  have h1 := bilinearDiagonalCutoff_support z hnonzero 1
  have hs0 : (z 0)^2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using (sq_le_sq₀ (abs_nonneg (z 0)) (by norm_num : (0 : ℝ) ≤ 2)).mpr h0
  have hs1 : (z 1)^2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using (sq_le_sq₀ (abs_nonneg (z 1)) (by norm_num : (0 : ℝ) ≤ 2)).mpr h1
  have hn : ‖z‖ ≤ 4 := by
    apply (sq_le_sq₀ (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 4)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    linarith only [hs0,hs1]
  exact hz (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn)

@[fun_prop] theorem bilinearDiagonalCutoff_contDiff : ContDiff ℝ ∞ bilinearDiagonalCutoff := by
  have hcoord (i : Fin 2) : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 2) => z i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff
  have hr : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 2) =>
      Fourier.chi0 ((z 0+z 1)/2) * Fourier.chi0 ((z 0-z 1)/2)) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp hr

/-- One absolute Fourier constant controls every translated diagonal shape. -/
theorem exists_bilinear_diagonal_lattice_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (c : EuclideanSpace ℝ (Fin 2)) (s r : Fin 2 → ℝ),
      ‖∑' p : Fin 2 → ℤ, bilinearDiagonalCutoff (WithLp.toLp 2 (fun i => (p i : ℝ)/L)-c) *
        e (∑ i, (s i*(p i : ℝ)^2+r i*(p i : ℝ)))‖ ≤
        C * ∏ i, weylSupremum (12*L) (s i) := by
  simpa only [show (4 : ℝ)*(2+1) = 12 by norm_num] using
    exists_translated_compact_lattice_bound bilinearDiagonalCutoff
      bilinearDiagonalCutoff_hasCompactSupport bilinearDiagonalCutoff_contDiff 2 (by norm_num)
      bilinearDiagonalCutoff_support

end WaveTurbulence.WeylSums

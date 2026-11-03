/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedDiagonalBound

/-! # Auxiliary-scale versions of the weighted diagonal bound -/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- The joint amplitude version of the pointwise Weyl reduction. All
spatial centers, linear frequencies and amplitudes are uniform; `C` depends
only on dimension. The auxiliary factor `Q≥1` is free, and its enlargement changes only the Weyl scale. This is a diagonal-coordinate intermediate theorem. -/
theorem exists_weighted_diagonal_bound_at_scale (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ (L width : ℝ), 1 ≤ L → 1 ≤ width →
      ∀ (c : EuclideanSpace ℝ (Fin d × Fin 2))
        (Φ : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ),
      ContDiff ℝ (10*d) Φ → ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ D) →
      ∀ u r w : Fin d → ℝ,
      let h : Fin d × Fin 2 → ℤ := fun i => round (L*c i)
      ‖∑' v : Fin d → ℤ × ℤ, pairParity h v *
        weightedDiagonalAmplitude Φ width c (pairLatticeSample L h v) *
        e (pairDiagonalPhase h u r w v)‖ ≤
      C*D*width^(2*d)*∏ j, weylSupremum (12*Q*width*L) (u j)^2 := by
  obtain ⟨C,hC,hfourier⟩ := exists_bilinear_amplitude_fourier_bound d hd
  refine ⟨C,hC,?_⟩
  intro Q hQ L width hL hw c Φ hΦ D hD hderiv u r w
  have hQp : 0 < Q := by linarith
  dsimp only
  let h : Fin d × Fin 2 → ℤ := fun i => round (L*c i)
  let M := 12*Q*width*L
  have hLp : 0 < L := by linarith
  have hwp : 0 < width := by linarith
  have hMp : 0 < M := by dsimp [M]; positivity
  obtain ⟨F,hF,hnorm,hrep⟩ := hfourier width hw c Φ hΦ D hD hderiv
  have hrep' (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
      weightedDiagonalAmplitude Φ width c z = ∫ ξ, F ξ*e (inner ℝ ξ z) := by
    simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using hrep z
  have hplateau (v : Fin d → ℤ × ℤ)
      (hv : weightedDiagonalAmplitude Φ width c (pairLatticeSample L h v) ≠ 0) (j : Fin d) :
      weylCutoff (((v j).1 : ℝ)/M) = 1 ∧ weylCutoff (((v j).2 : ℝ)/M) = 1 := by
    have hcoord (n : ℤ) (i : Fin d × Fin 2)
        (hh : |((n+h i : ℤ) : ℝ)/L-c i| ≤ 2*width) : weylCutoff ((n : ℝ)/M) = 1 := by
      have hr := abs_sub_round (L*c i)
      change |L*c i-(h i : ℝ)| ≤ 1/2 at hr
      obtain ⟨hl,hu⟩ := abs_le.mp hh
      obtain ⟨hrl,hru⟩ := abs_le.mp hr
      push_cast at hl hu
      have hlo := (le_div_iff₀ hLp).mp (show c i-2*width ≤ ((n : ℝ)+h i)/L by linarith)
      have hhi := (div_le_iff₀ hLp).mp (show ((n : ℝ)+h i)/L ≤ c i+2*width by linarith)
      have hn : |(n : ℝ)/M| ≤ 1/2 := by
        rw [abs_div, abs_of_pos hMp, div_le_iff₀ hMp]
        apply abs_le.mpr
        dsimp [M]
        have hwL : 1 ≤ width*L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hL),hw,hL]
        have hQM : width*L ≤ Q*width*L := by
          have hh := mul_nonneg (sub_nonneg.mpr hQ) (mul_nonneg hwp.le hLp.le)
          nlinarith only [hh]
        constructor <;> nlinarith only [hlo,hhi,hrl,hru,hwL,hQM]
      simp only [weylCutoff, Fourier.chi0_eq_one hn, Complex.ofReal_one]
    constructor
    · apply hcoord (v j).1 (j,0)
      simpa only [pairLatticeSample_apply_zero] using
        weightedDiagonalAmplitude_support Φ hwp c _ hv (j,0)
    · apply hcoord (v j).2 (j,1)
      simpa only [pairLatticeSample_apply_one] using
        weightedDiagonalAmplitude_support Φ hwp c _ hv (j,1)
  exact (norm_pair_lattice_le_of_fourier_representation _ F hF hrep' L M h hMp
    hplateau u r w).trans (mul_le_mul_of_nonneg_right hnorm
      (prod_nonneg (fun j hj => sq_nonneg _)))

/-- The same bound on the original diagonal integer lattice. Integer
recentering is an exact reindexing, including its parity projectors. -/
theorem exists_weighted_diagonal_uncentered_bound_at_scale (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ (L width : ℝ), 1 ≤ L → 1 ≤ width →
      ∀ (c : EuclideanSpace ℝ (Fin d × Fin 2))
        (Φ : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ),
      ContDiff ℝ (10*d) Φ → ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ D) →
      ∀ u r w : Fin d → ℝ,
      ‖∑' v : Fin d → ℤ × ℤ, pairParity (fun _ => 0) v *
        weightedDiagonalAmplitude Φ width c (pairLatticeSample L (fun _ => 0) v) *
        e (pairDiagonalPhase (fun _ => 0) u r w v)‖ ≤
      C*D*width^(2*d)*∏ j, weylSupremum (12*Q*width*L) (u j)^2 := by
  obtain ⟨C,hC,hb⟩ := exists_weighted_diagonal_bound_at_scale d hd
  refine ⟨C,hC,?_⟩
  intro Q hQ L width hL hw c Φ hΦ D hD hderiv u r w
  have hQp : 0 < Q := by linarith
  let h : Fin d × Fin 2 → ℤ := fun i => round (L*c i)
  let hp : Fin d → ℤ × ℤ := fun j => (h (j,0),h (j,1))
  have hh := hb Q hQ L width hL hw c Φ hΦ D hD hderiv u r w
  have heq := (Equiv.addRight hp).tsum_eq (fun v : Fin d → ℤ × ℤ =>
    pairParity (fun _ => 0) v *
      weightedDiagonalAmplitude Φ width c (pairLatticeSample L (fun _ => 0) v) *
      e (pairDiagonalPhase (fun _ => 0) u r w v))
  have heq' : (∑' v : Fin d → ℤ × ℤ, pairParity h v *
      weightedDiagonalAmplitude Φ width c (pairLatticeSample L h v) *
      e (pairDiagonalPhase h u r w v)) =
    ∑' v : Fin d → ℤ × ℤ, pairParity (fun _ => 0) v *
      weightedDiagonalAmplitude Φ width c (pairLatticeSample L (fun _ => 0) v) *
      e (pairDiagonalPhase (fun _ => 0) u r w v) := by
    simpa only [Equiv.coe_addRight, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      hp, pairParity, pairLatticeSample, pairDiagonalPhase, Int.cast_zero, add_zero, Int.cast_add] using heq
  rw [← heq']
  exact hh

end WaveTurbulence.WeylSums

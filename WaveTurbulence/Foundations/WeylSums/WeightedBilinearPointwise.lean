/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearPacking
public import WaveTurbulence.Foundations.WeylSums.WeightedDiagonalBound

/-! # Joint-amplitude pointwise bound for DH23 Lemma 6.6 -/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- Exact phase identity in all coordinates, including arbitrary linear frequencies. -/
theorem pairDiagonalPhase_diagonalize {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (s : ℝ) (ξ ζ : Mom d) (v : Fin d → ℤ × ℤ) :
    pairDiagonalPhase (fun _ => 0) (fun _ => s/(4*L^2))
      (fun j => (ξ j+ζ j)/(2*L)) (fun j => (ξ j-ζ j)/(2*L)) (pairDiagonalize v) =
      inner ℝ (latticePoint L (fun j => (v j).1)) ξ +
      inner ℝ (latticePoint L (fun j => (v j).2)) ζ +
      s*inner ℝ (latticePoint L (fun j => (v j).1)) (latticePoint L (fun j => (v j).2)) := by
  simp only [pairDiagonalPhase, pairDiagonalize, Int.cast_zero, add_zero, Int.cast_add,
    Int.cast_sub, PiLp.inner_apply, Real.inner_apply, latticePoint,
    ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j hj
  field_simp [hL]
  ring

/-- The source weighted sum is exactly the parity-lattice Fourier reduction. -/
theorem weightedBilinearLatticeSum_eq_diagonal {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (Φ : ℝ → Mom d → Mom d → ℂ) (width s : ℝ) (a b ξ ζ : Mom d) :
    weightedBilinearLatticeSum Φ L width s a b ξ ζ =
      ∑' v : Fin d → ℤ × ℤ, pairParity (fun _ => 0) v *
        weightedDiagonalAmplitude (packedBilinearAmplitude (Φ s)) width
          (diagonalBilinearCenter a b) (pairLatticeSample L (fun _ => 0) v) *
        e (pairDiagonalPhase (fun _ => 0) (fun _ => s/(4*L^2))
          (fun j => (ξ j+ζ j)/(2*L)) (fun j => (ξ j-ζ j)/(2*L)) v) := by
  let E := Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ℤ) (fun _ => ℤ)
  let F (v : Fin d → ℤ × ℤ) :=
    weightedDiagonalAmplitude (packedBilinearAmplitude (Φ s)) width
      (diagonalBilinearCenter a b) (pairLatticeSample L (fun _ => 0) v) *
      e (pairDiagonalPhase (fun _ => 0) (fun _ => s/(4*L^2))
        (fun j => (ξ j+ζ j)/(2*L)) (fun j => (ξ j-ζ j)/(2*L)) v)
  have heq : weightedBilinearLatticeSum Φ L width s a b ξ ζ =
      ∑' v : Fin d → ℤ × ℤ, F (pairDiagonalize v) := by
    unfold weightedBilinearLatticeSum
    rw [← E.tsum_eq]
    apply tsum_congr
    intro v
    dsimp only [F]
    rw [weightedDiagonalAmplitude_pairDiagonalize hL, pairDiagonalPhase_diagonalize hL]
    simp only [E, Equiv.arrowProdEquivProdArrow_apply]
    ring
  rw [heq, tsum_pair_diagonalize]
  apply tsum_congr
  intro v
  dsimp only [F]
  ring

/-- Uniform weighted bilinear pointwise bound from finite spatial derivative
bounds. The derivatives are measured on the joint physical Euclidean space;
no time differentiability is required. -/
theorem exists_weightedBilinearLatticeSum_pointwise_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L width : ℝ), 1 ≤ L → 1 ≤ width →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ) (s : ℝ),
      ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s)) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ D) →
      ∀ a b ξ ζ : Mom d,
      ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖ ≤
        C*D*width^(2*d)*weylSupremum (12*width*L) (s/(4*L^2))^(2*d) := by
  obtain ⟨C,hC,hb⟩ := exists_weighted_diagonal_uncentered_bound d hd
  refine ⟨C,hC,?_⟩
  intro L width hL hw Φ s hΦ D hD hderiv a b ξ ζ
  have hLp : 0 < L := by linarith
  rw [weightedBilinearLatticeSum_eq_diagonal hLp.ne']
  have hh := hb L width hL hw (diagonalBilinearCenter a b)
    (packedBilinearAmplitude (Φ s)) hΦ D hD hderiv
    (fun _ => s/(4*L^2)) (fun j => (ξ j+ζ j)/(2*L)) (fun j => (ξ j-ζ j)/(2*L))
  simpa only [prod_const, card_univ, Fintype.card_fin, ← pow_mul] using hh

end WaveTurbulence.WeylSums

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearPacking
public import WaveTurbulence.Foundations.WeylSums.WeightedDiagonalScale
public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearPointwise

/-! # Auxiliary-scale joint-amplitude bound for DH23 Lemma 6.6 -/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- Uniform weighted bilinear pointwise bound from finite spatial derivative
bounds. The derivatives are measured on the joint physical Euclidean space;
no time differentiability is required. The auxiliary scale is `12*Q*width*L` for any `Q≥1`. -/
theorem exists_weightedBilinearLatticeSum_pointwise_bound_at_scale (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ (L width : ℝ), 1 ≤ L → 1 ≤ width →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ) (s : ℝ),
      ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s)) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ D) →
      ∀ a b ξ ζ : Mom d,
      ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖ ≤
        C*D*width^(2*d)*weylSupremum (12*Q*width*L) (s/(4*L^2))^(2*d) := by
  obtain ⟨C,hC,hb⟩ := exists_weighted_diagonal_uncentered_bound_at_scale d hd
  refine ⟨C,hC,?_⟩
  intro Q hQ L width hL hw Φ s hΦ D hD hderiv a b ξ ζ
  have hLp : 0 < L := by linarith
  rw [weightedBilinearLatticeSum_eq_diagonal hLp.ne']
  have hh := hb Q hQ L width hL hw (diagonalBilinearCenter a b)
    (packedBilinearAmplitude (Φ s)) hΦ D hD hderiv
    (fun _ => s/(4*L^2)) (fun j => (ξ j+ζ j)/(2*L)) (fun j => (ξ j-ζ j)/(2*L))
  simpa only [prod_const, card_univ, Fintype.card_fin, ← pow_mul] using hh

end WaveTurbulence.WeylSums

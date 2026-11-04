/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-!
# Operator norm from the actual coordinate derivative values

Finite multilinear expansion gives the dimension-dependent bridge from
the source's coordinate-word spatial norm to derivative-integral bounds.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Coordinate values control a multilinear operator, with the exact `d^j` finite sum loss. -/
theorem multilinear_norm_le_of_coordinate_bound {d j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Mom d) ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ ρ : Fin j → Fin d, ‖A (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤ M) :
    ‖A‖ ≤ (d : ℝ) ^ j * M := by
  classical
  have hx (x : Mom d) : (∑ i : Fin d, x i • EuclideanSpace.single i 1) = x := by
    ext k
    simp [Pi.single_apply]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : A v = ∑ ρ : Fin j → Fin d,
      (∏ i, v i (ρ i)) • A (fun i => EuclideanSpace.single (ρ i) 1) := by
    calc
      _ = A (fun i => ∑ k : Fin d, v i k • EuclideanSpace.single k 1) := by
        congr 1
        exact funext (fun i => (hx (v i)).symm)
      _ = ∑ ρ : Fin j → Fin d, A (fun i => v i (ρ i) • EuclideanSpace.single (ρ i) 1) :=
        A.toMultilinearMap.map_sum _
      _ = _ := Finset.sum_congr rfl (fun ρ _ => A.toMultilinearMap.map_smul_univ _ _)
  calc
    ‖A v‖ ≤ ∑ ρ : Fin j → Fin d,
        ‖(∏ i, v i (ρ i)) • A (fun i => EuclideanSpace.single (ρ i) 1)‖ := by
      rw [he]
      exact norm_sum_le _ _
    _ ≤ ∑ _ρ : Fin j → Fin d, (∏ i, ‖v i‖) * M := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [norm_smul, norm_prod]
      apply mul_le_mul _ (hA ρ) (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
      exact PiLp.norm_apply_le (v i) (ρ i)
    _ = ((d : ℝ) ^ j * M) * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

end WaveTurbulence.Incoh

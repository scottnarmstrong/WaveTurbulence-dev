/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicScalarSmall
public import WaveTurbulence.Foundations.LemLin.CubicTensor
public import WaveTurbulence.Foundations.WeylSums.CubicTensor
public import WaveTurbulence.Foundations.WeylSums.CubicDiagonalSum
import Mathlib.Tactic

/-!
# The source cubic lattice sum on its small-time region

Both source quadratic forms are matched literally with the landed
scalar cubic phase. Tensor factorization then gives the dimension-d
stationary-phase gain with unrestricted centers and modulations.
-/

public section

namespace WaveTurbulence.Sumint

/-- The Boolean convention of the source cubic sum. -/
@[expose] def cubicKind (sel : Bool) : LemLin.CubicPhase :=
  if sel then .cross else .collision

/-- The actual scalar series is exactly the source's three-variable Weyl series. -/
theorem scalarCubic_sum_eq_weyl (L s t : ℝ) (sel : Bool) (a b c ξ ζ ω : ℝ) :
    (∑' m : Fin 3 → ℤ,
      translatedCubicAmplitude (cubicKind sel) LemLin.fixedCubicCutoffs s t ![a,b,c] ![ξ,ζ,ω]
        (fun j => (m j : ℝ)/L)) = WeylSums.scalarCubicSum L t s sel a b c ξ ζ ω := by
  rw [← WeylSums.tripleCoordinatesEquiv.symm.tsum_eq]
  unfold WeylSums.scalarCubicSum
  apply tsum_congr
  intro q
  have he : WeylSums.tripleCoordinatesEquiv.symm q = ![q.1, q.2.1, q.2.2] := rfl
  rw [he]
  cases sel <;>
    simp [translatedCubicAmplitude, LemLin.cubicProduct, LemLin.fixedCubicCutoffs,
      LemLin.fixedScalarCutoff, LemLin.scalarQuadratic, cubicKind,
      Fourier.chi0Complex, WeylSums.scalarCubicTerm, WeylSums.e,
      Fin.prod_univ_succ, Fin.sum_univ_succ, Real.fourierChar_apply]
  all_goals
    apply congrArg₂ (fun u v : ℂ => u * v)
    · simp [mul_comm, mul_left_comm, mul_assoc]
    · congr 1
      push_cast
      ring

/-- Both scalar source phases satisfy the same small-time bound. -/
theorem exists_scalar_weyl_cubic_small_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ s t : ℝ, |s| ≤ L → |t| ≤ L →
    ∀ (sel : Bool) (a b c ξ ζ ω : ℝ),
      ‖WeylSums.scalarCubicSum L t s sel a b c ξ ζ ω‖ ≤
        C * L^3 / (1+|s|+|t|) := by
  obtain ⟨C, hC, hb⟩ := exists_scalar_cubic_small_bound LemLin.fixedCubicCutoffs
  refine ⟨C, hC, ?_⟩
  intro L hL s t hs ht sel a b c ξ ζ ω
  rw [← scalarCubic_sum_eq_weyl]
  exact hb hL (cubicKind sel) s t hs ht ![a,b,c] ![ξ,ζ,ω]

/-- The exact source three-vector sum gains one power per spatial coordinate. -/
theorem exists_cubic_weyl_small_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ s t : ℝ, |s| ≤ L → |t| ≤ L →
    ∀ (sel : Bool) (a b c ξ ζ ω : Mom d),
      ‖WeylSums.cubicLatticeSum L t s sel a b c ξ ζ ω‖ ≤
        C * L^(3*d) / (1+|s|+|t|)^d := by
  obtain ⟨C, hC, hb⟩ := exists_scalar_weyl_cubic_small_bound
  refine ⟨C^d, pow_nonneg hC _, ?_⟩
  intro L hL s t hs ht sel a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  rw [WeylSums.cubicLatticeSum_eq_prod hLp, norm_prod]
  calc
    _ ≤ ∏ _j : Fin d, C * L^3 / (1+|s|+|t|) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb hL s t hs ht sel _ _ _ _ _ _)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, mul_pow, ← pow_mul]

end WaveTurbulence.Sumint

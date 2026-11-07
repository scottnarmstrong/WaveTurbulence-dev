/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PiProd

/-! # Expansion of a clocked `sumint` expression into modes (engine step EXP, interchange)

Given Fourier-series expansions `W_ρ(s,k) = ∑_m c_ρ(m,k) e^{πi m·s}` of the clocked weights, the clocked
`sumint` expression is the sum over mode tuples of `e^{πi ν_m · tt} · signedExpr (modeDatum ..)`, with the
interchange of `∑_x`, `∫_τ`, `∑_m` justified by the summable majorant `S ρ m · Dec ρ k`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem continuous_slotVal (tt : Fin 3 → ℝ) (s : Slot D) : Continuous fun τ : D.S.TVar → ℝ => slotVal D τ tt s := by
  cases s with
  | inl v => exact continuous_apply v
  | inr c => exact continuous_const

theorem continuous_fsPhase_clock (cr : ClockedRows D) (tt : Fin 3 → ℝ) (ρ : Row D) (m : Fin 2 → ℤ) :
    Continuous fun τ : D.S.TVar → ℝ => fsPhase m (cr.clock τ tt ρ) := by
  have : (fun τ : D.S.TVar → ℝ => fsPhase m (cr.clock τ tt ρ)) = fun τ =>
      Complex.exp ((Real.pi * ∑ i, (m i : ℝ) * cr.clock τ tt ρ i : ℝ) * Complex.I) :=
    funext fun τ => fsPhase_eq_exp m _
  rw [this]
  refine Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const)
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul ?_)
  exact continuous_slotVal tt _

theorem norm_fsPhase (m : Fin 2 → ℤ) (t : Fin 2 → ℝ) : ‖fsPhase m t‖ = 1 := by
  unfold fsPhase; exact Circle.norm_coe _


/-- The mode term of the interchange. -/
noncomputable def modeTerm (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (m : Row D → Fin 2 → ℤ) (τ : D.S.TVar → ℝ) : ℂ :=
  D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
    ((∏ ρ, c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)) * ∏ ρ, fsPhase (m ρ) (cr.clock τ tt ρ))

theorem norm_modeTerm_le (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ) (hbad : ∀ i, D.badKind i ≠ 2)
    (hS0 : ∀ ρ m, 0 ≤ S ρ m) (hDec0 : ∀ ρ k, 0 ≤ Dec ρ k)
    (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (m : Row D → Fin 2 → ℤ) (τ : D.S.TVar → ℝ) :
    ‖modeTerm cr c L γ δ η x E tt m τ‖ ≤
      (∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ) := by
  unfold modeTerm
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_fsPhase, Finset.prod_const_one, mul_one]
  have h1 := norm_phase_le D hbad L γ δ η x (E 0 - E 1) (tt 0) τ
  have h2 : ∏ ρ, ‖c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)‖ ≤ ∏ ρ, (S ρ (m ρ) * Dec ρ (rowMom D L x E ρ)) :=
    by gcongr with ρ hρ; exact hcS _ _ _ _
  have h3 : ∏ ρ, (S ρ (m ρ) * Dec ρ (rowMom D L x E ρ)) =
      (∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ) := by
    rw [Finset.prod_mul_distrib, mul_comm]
  calc ‖D.phase L γ δ η x (E 0 - E 1) (tt 0) τ‖ *
        ∏ ρ, ‖c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)‖
      ≤ 1 * ((∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ)) :=
        mul_le_mul h1 (h2.trans_eq h3) (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end WaveTurbulence.VineEstS3Par.Eng

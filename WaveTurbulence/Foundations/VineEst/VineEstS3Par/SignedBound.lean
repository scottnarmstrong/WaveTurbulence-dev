/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.SignedParam

/-! # `signedPhase` is continuous in the times and unimodular (no bad case (c)) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.SumintPar Finset
open scoped ENNReal

variable {d : ℕ}

theorem continuous_phase (D : SumintPar.SumintDatum d) (hbad : ∀ i, D.badKind i ≠ 2)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) : Continuous (D.phase L γ δ η x r t) := by
  have h : ∀ i, ¬ (D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i) := fun i h => hbad i h.2.1
  unfold SumintPar.SumintDatum.phase
  simp only [h, dite_false]
  fun_prop

theorem norm_phase_le (D : SumintPar.SumintDatum d) (hbad : ∀ i, D.badKind i ≠ 2)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) : ‖D.phase L γ δ η x r t τ‖ ≤ 1 := by
  have h : ∀ i, ¬ (D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i) := fun i h => hbad i h.2.1
  unfold SumintPar.SumintDatum.phase
  simp only [h, dite_false, norm_mul, norm_prod, Complex.norm_exp_ofReal_mul_I,
    Finset.prod_const_one, mul_one, one_mul, norm_one]
  exact le_refl _

end WaveTurbulence.VineEstS3Par.Eng

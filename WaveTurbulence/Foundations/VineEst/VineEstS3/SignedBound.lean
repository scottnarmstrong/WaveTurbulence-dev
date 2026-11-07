/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.SignedParam

/-! # `signedPhase` is continuous in the times and unimodular (no bad case (c)) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.VineEstS2 Finset
open scoped ENNReal

variable {d : ℕ}

theorem continuous_signedPhase (D : SumintDatum d) (hbad : ∀ i, D.badKind i ≠ 2)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) : Continuous (signedPhase D coreFirstSign coreSign L γ δ η x r t) := by
  have h : ∀ i, ¬ (D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i) := fun i h => hbad i h.2.1
  unfold signedPhase
  simp only [h, dite_false]
  fun_prop

theorem norm_signedPhase_le (D : SumintDatum d) (hbad : ∀ i, D.badKind i ≠ 2)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) : ‖signedPhase D coreFirstSign coreSign L γ δ η x r t τ‖ ≤ 1 := by
  have h : ∀ i, ¬ (D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i) := fun i h => hbad i h.2.1
  unfold signedPhase
  simp only [h, dite_false, norm_mul, norm_prod, Complex.norm_exp_ofReal_mul_I,
    Finset.prod_const_one, mul_one, one_mul, norm_one]
  exact le_refl _

end WaveTurbulence.VineEstS3.Eng

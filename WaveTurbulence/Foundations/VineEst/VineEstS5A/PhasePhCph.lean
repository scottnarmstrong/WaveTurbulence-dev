/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.SignedBound

/-! # Kind-2 phase: continuity and the norm of `signedPhase` (V5 Step 4d-A, item 1)

For a bad block of kind 2 the phase carries the factor `|t₁ - s₁|^(1-3η)`.  For `3η ≤ 1` the phase is still
continuous; its norm is the product `kind2Factor` of these factors, independent of `x, r, t`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.SumintPar Finset

variable {d : ℕ}

/-- The product of the kind-2 factors `|t₁ⁱ - s₁ⁱ|^(1-3η)` (norm of the phase). -/
noncomputable def kind2Factor (D : SumintPar.SumintDatum d) (η : ℝ) (τ : D.S.TVar → ℝ) : ℝ :=
  ∏ i, (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
    |τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) else 1)

theorem norm_phase_eq (D : SumintPar.SumintDatum d) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) : ‖D.phase L γ δ η x r t τ‖ = kind2Factor D η τ := by
  unfold SumintPar.SumintDatum.phase kind2Factor
  simp only [norm_mul, norm_prod, Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one, mul_one, one_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  · simp

theorem continuous_phase_of_le (D : SumintPar.SumintDatum d) (L γ δ η : ℝ) (hη : 3 * η ≤ 1)
    (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) : Continuous (D.phase L γ δ η x r t) := by
  have hq : (0 : ℝ) ≤ 1 - 3 * η := by linarith
  unfold SumintPar.SumintDatum.phase
  have key : ∀ i : Fin D.S.I, Continuous fun τ : D.S.TVar → ℝ =>
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1) := by
    intro i
    by_cases h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i
    · simp only [h, and_self, dite_true]
      refine Complex.continuous_ofReal.comp ?_
      exact Continuous.rpow_const (by fun_prop) (fun _ => Or.inr hq)
    · simp only [h, dite_false]; exact continuous_const
  fun_prop (disch := first | exact key _ | skip)

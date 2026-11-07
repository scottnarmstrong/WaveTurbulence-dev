/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PhaseNorm
public import WaveTurbulence.Foundations.SumintPar.LocalPhaseExtension
import Mathlib.Tactic

/-!
# Input-time measurability and integrability of the literal source phase

For η≤1/3 the case (c) exponent is nonnegative. Its norm is continuous,
and hence integrable on the fixed compact input box. The full phase is
measurable without imposing extra regularity on any source weights.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The exact source phase is measurable in all input times. -/
theorem measurable_phase {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) :
    Measurable (D.phase L γ δ η x r t) := by
  classical
  unfold SumintDatum.phase
  fun_prop

/-- Its norm is continuous whenever the explicit case (c) power is nonnegative. -/
theorem continuous_norm_phase {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) :
    Continuous (fun τ => ‖D.phase L γ δ η x r t τ‖) := by
  classical
  simp_rw [norm_phase]
  apply continuous_finsetProd
  intro i _
  by_cases hi : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i
  · simp only [dite_eq_left hi]
    have ht : Continuous (fun τ : D.S.TVar → ℝ => τ (.inl ⟨i, ⟨1, by omega⟩⟩)) := continuous_apply _
    have hs : Continuous (fun τ : D.S.TVar → ℝ => τ (.inr (.inl ⟨i, ⟨0, hi.2.2⟩⟩))) := continuous_apply _
    exact (ht.sub hs).abs.rpow_const (fun _ => Or.inr (by linarith only [hη]))
  · simp only [dite_eq_right hi]
    exact continuous_const

/-- The source phase is genuinely integrable on every fixed enlarged input box. -/
theorem integrableOn_phase_enlargedBox {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t c h : ℝ) :
    IntegrableOn (D.phase L γ δ η x r t) (enlargedInputTimeBox D c h) := by
  have hn : IntegrableOn (fun τ => ‖D.phase L γ δ η x r t τ‖)
      (enlargedInputTimeBox D c h) :=
    (continuous_norm_phase D L γ δ η hη x r t).integrableOn_Icc
  exact hn.mono' (measurable_phase D L γ δ η x r t).aestronglyMeasurable.restrict
    (ae_of_all _ (fun _ => le_rfl))

/-- Restricting to the static source inequalities preserves input-time integrability. -/
theorem integrableOn_phase_localDomain {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (hη : η ≤ 1/3) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t c h : ℝ) :
    IntegrableOn (D.phase L γ δ η x r t) (localInputTimeDomain D c h) :=
  (integrableOn_phase_enlargedBox D L γ δ η hη x r t c h).mono_set Set.inter_subset_left

end WaveTurbulence.SumintPar

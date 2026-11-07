/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! **FINALCOUNT-ASSEMBLY, B/C: the abstract cover induction.**  States `St` with a well-founded order `lt`, classes `A : Set Dec`
(of decorations), a quantity `Q h A ∈ [0,∞]` that is monotone in `A`, subadditive over unions and zero on `∅`, and a potential `W`.
If at every non-final `(h, A)` the class is covered by `≤ N` subclasses `A' j`, each reached by a step `h → h' j` with
`Q h (A' j) ≤ I j * Q (h' j) (A' j)` and `N * (I j * W (h' j)) ≤ W h`, and the final classes satisfy `Q h A ≤ W h`, then `Q h A ≤ W h`
everywhere.  This is the class decomposition + chain induction of the assembly (PLAN §B/C); the concrete content is in the hypotheses. -/
@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm

theorem Q_iUnion_le {St Dec ι : Type*} (Q : St → Set Dec → ℝ≥0∞) (hunion : ∀ h A B, Q h (A ∪ B) ≤ Q h A + Q h B)
    (hempty : ∀ h, Q h ∅ = 0) (h : St) (S : Finset ι) (A : ι → Set Dec) :
    Q h (⋃ j ∈ S, A j) ≤ ∑ j ∈ S, Q h (A j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (hunion _ _ _).trans (add_le_add_right ih _)

theorem cover_induction {St Dec ι : Type*} (lt : St → St → Prop) (wf : WellFounded lt)
    (Inv : St → Set Dec → Prop) (Fin' : St → Set Dec → Prop) (Q : St → Set Dec → ℝ≥0∞) (W : St → ℝ≥0∞)
    (N : ℕ) (hN : 1 ≤ N)
    (hmono : ∀ h A B, A ⊆ B → Q h A ≤ Q h B)
    (hunion : ∀ h A B, Q h (A ∪ B) ≤ Q h A + Q h B) (hempty : ∀ h, Q h ∅ = 0)
    (hfin : ∀ h A, Inv h A → Fin' h A → Q h A ≤ W h)
    (hstep : ∀ h A, Inv h A → ¬ Fin' h A → ∃ (S : Finset ι) (A' : ι → Set Dec) (h' : ι → St) (I : ι → ℝ≥0∞),
      A ⊆ (⋃ j ∈ S, A' j) ∧ S.card ≤ N ∧ ∀ j ∈ S, lt (h' j) h ∧ Inv (h' j) (A' j) ∧
        Q h (A' j) ≤ I j * Q (h' j) (A' j) ∧ N * (I j * W (h' j)) ≤ W h) :
    ∀ h A, Inv h A → Q h A ≤ W h := by
  intro h
  induction h using wf.induction with
  | _ h ih =>
    intro A hA
    by_cases hf : Fin' h A
    · exact hfin h A hA hf
    obtain ⟨S, A', h', I, hcov, hS, hj⟩ := hstep h A hA hf
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    have key : ∀ j ∈ S, Q h (A' j) ≤ W h / N := by
      intro j hjS
      obtain ⟨hlt, hinv, hdev, hw⟩ := hj j hjS
      have h1 : Q (h' j) (A' j) ≤ W (h' j) := ih _ hlt _ hinv
      calc Q h (A' j) ≤ I j * Q (h' j) (A' j) := hdev
        _ ≤ I j * W (h' j) := by gcongr
        _ ≤ W h / N := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNt), mul_comm]; exact hw
    calc Q h A ≤ Q h (⋃ j ∈ S, A' j) := hmono _ _ _ hcov
      _ ≤ ∑ j ∈ S, Q h (A' j) := Q_iUnion_le Q hunion hempty h S A'
      _ ≤ ∑ j ∈ S, W h / N := Finset.sum_le_sum key
      _ = S.card * (W h / N) := by simp
      _ ≤ N * (W h / N) := by gcongr
      _ = W h := ENNReal.mul_div_cancel hN0 hNt

end WaveTurbulence.FinalCountAsm

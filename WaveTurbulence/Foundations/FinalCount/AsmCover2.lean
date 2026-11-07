/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCover
/-! **FINALCOUNT-ASSEMBLY, B/C: the cover induction with a terminal piece.**  Variant of `cover_induction` in which, at a
non-final `(h, A)`, the class splits as a terminal piece `Afin` (on which `Fin'` holds) and `≤ N - 1` step pieces.  The terminal piece
is bounded by `W h / N` (`hfin`: `N * Q h A ≤ W h` on final classes), each step piece by `W h / N`. -/
@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm

theorem cover_induction2 {St Dec ι : Type*} (lt : St → St → Prop) (wf : WellFounded lt)
    (Inv : St → Set Dec → Prop) (Fin' : St → Set Dec → Prop) (Q : St → Set Dec → ℝ≥0∞) (W : St → ℝ≥0∞)
    (N : ℕ) (hN : 1 ≤ N)
    (hmono : ∀ h A B, A ⊆ B → Q h A ≤ Q h B)
    (hunion : ∀ h A B, Q h (A ∪ B) ≤ Q h A + Q h B) (hempty : ∀ h, Q h ∅ = 0)
    (hfin : ∀ h A, Inv h A → Fin' h A → N * Q h A ≤ W h)
    (hstep : ∀ h A, Inv h A → ¬ Fin' h A → ∃ (Afin : Set Dec) (S : Finset ι) (A' : ι → Set Dec) (h' : ι → St)
      (I : ι → ℝ≥0∞),
      Inv h Afin ∧ Fin' h Afin ∧ A ⊆ Afin ∪ (⋃ j ∈ S, A' j) ∧ S.card + 1 ≤ N ∧ ∀ j ∈ S, lt (h' j) h ∧
        Inv (h' j) (A' j) ∧ Q h (A' j) ≤ I j * Q (h' j) (A' j) ∧ N * (I j * W (h' j)) ≤ W h) :
    ∀ h A, Inv h A → Q h A ≤ W h := by
  intro h
  induction h using wf.induction with
  | _ h ih =>
    intro A hA
    by_cases hf : Fin' h A
    · have := hfin h A hA hf
      have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      calc Q h A = 1 * Q h A := by simp
        _ ≤ N * Q h A := by gcongr; exact_mod_cast hN
        _ ≤ W h := this
    obtain ⟨Afin, S, A', h', I, hinv, hfa, hcov, hS, hj⟩ := hstep h A hA hf
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    have key : ∀ j ∈ S, Q h (A' j) ≤ W h / N := by
      intro j hjS
      obtain ⟨hlt, hinv', hdev, hw⟩ := hj j hjS
      have h1 : Q (h' j) (A' j) ≤ W (h' j) := ih _ hlt _ hinv'
      calc Q h (A' j) ≤ I j * Q (h' j) (A' j) := hdev
        _ ≤ I j * W (h' j) := by gcongr
        _ ≤ W h / N := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNt), mul_comm]; exact hw
    have kfin : Q h Afin ≤ W h / N := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNt), mul_comm]; exact hfin h Afin hinv hfa
    calc Q h A ≤ Q h (Afin ∪ ⋃ j ∈ S, A' j) := hmono _ _ _ hcov
      _ ≤ Q h Afin + Q h (⋃ j ∈ S, A' j) := hunion _ _ _
      _ ≤ W h / N + ∑ j ∈ S, W h / N :=
          add_le_add kfin ((Q_iUnion_le Q hunion hempty h S A').trans (Finset.sum_le_sum key))
      _ = (S.card + 1) * (W h / N) := by simp; ring
      _ ≤ N * (W h / N) := by gcongr; exact_mod_cast hS
      _ = W h := ENNReal.mul_div_cancel hN0 hNt

end WaveTurbulence.FinalCountAsm

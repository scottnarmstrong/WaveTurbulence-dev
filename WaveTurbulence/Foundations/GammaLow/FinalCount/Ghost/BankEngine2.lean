/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.BankEngine
/-! **Ghost assembly: the cover induction with weighted children** (design: `CHAIN-DESIGN.md`).

`cover_induction_wt`: `cover_induction_split` with a weight `m j` per child: the child `j` has the budget
`m j / (K·N)` (`(K·N)·I j·W(child) ≤ m j · W`), and the weights of a step add up to at most `K·(N - 1)`
(`∑ m + K ≤ K·N`). A split node gives each of its `≤ K` children the weight `1`; an unsplit node gives its one
child the weight `K` (budget `1/N`, as in main's `cover_induction2`); an empty child has weight `0` and cost `0`. -/
@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence.FinalCountAsm

theorem cover_induction_wt {St Dec ι : Type*} (lt : St → St → Prop) (wf : WellFounded lt)
    (Inv : St → Set Dec → Prop) (Fin' : St → Set Dec → Prop) (Q : St → Set Dec → ℝ≥0∞) (W : St → ℝ≥0∞)
    (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hmono : ∀ h A B, A ⊆ B → Q h A ≤ Q h B)
    (hunion : ∀ h A B, Q h (A ∪ B) ≤ Q h A + Q h B) (hempty : ∀ h, Q h ∅ = 0)
    (hfin : ∀ h A, Inv h A → Fin' h A → N * Q h A ≤ W h)
    (hstep : ∀ h A, Inv h A → ¬ Fin' h A → ∃ (Afin : Set Dec) (S : Finset ι) (A' : ι → Set Dec) (h' : ι → St)
      (I : ι → ℝ≥0∞) (m : ι → ℕ),
      Inv h Afin ∧ Fin' h Afin ∧ A ⊆ Afin ∪ (⋃ j ∈ S, A' j) ∧ (∑ j ∈ S, m j) + K ≤ K * N ∧ ∀ j ∈ S, lt (h' j) h ∧
        Inv (h' j) (A' j) ∧ Q h (A' j) ≤ I j * Q (h' j) (A' j) ∧
        ((K * N : ℕ) : ℝ≥0∞) * (I j * W (h' j)) ≤ (m j : ℝ≥0∞) * W h) :
    ∀ h A, Inv h A → Q h A ≤ W h := by
  have hKN0 : ((K * N : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : K * N ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    exact_mod_cast this
  have hKNt : ((K * N : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  intro h
  induction h using wf.induction with
  | _ h ih =>
    intro A hA
    set u : ℝ≥0∞ := W h / ((K * N : ℕ) : ℝ≥0∞) with hu
    have hfinK : ∀ B, Inv h B → Fin' h B → Q h B ≤ K * u := by
      intro B hB hf
      have h1 := hfin h B hB hf
      rw [hu, ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hKN0) (Or.inl hKNt)]
      calc Q h B * ((K * N : ℕ) : ℝ≥0∞) = (K : ℝ≥0∞) * ((N : ℝ≥0∞) * Q h B) := by push_cast; ring
        _ ≤ K * W h := by gcongr
    by_cases hf : Fin' h A
    · calc Q h A ≤ K * u := hfinK A hA hf
        _ ≤ ((K * N : ℕ) : ℝ≥0∞) * u := by
          gcongr
          exact_mod_cast Nat.le_mul_of_pos_right K (by omega)
        _ = W h := by rw [hu]; exact ENNReal.mul_div_cancel hKN0 hKNt
    obtain ⟨Afin, S, A', h', I, m, hinv, hfa, hcov, hS, hj⟩ := hstep h A hA hf
    have key : ∀ j ∈ S, Q h (A' j) ≤ (m j : ℝ≥0∞) * u := by
      intro j hjS
      obtain ⟨hlt, hinv', hdev, hw⟩ := hj j hjS
      have h1 : Q (h' j) (A' j) ≤ W (h' j) := ih _ hlt _ hinv'
      calc Q h (A' j) ≤ I j * Q (h' j) (A' j) := hdev
        _ ≤ I j * W (h' j) := by gcongr
        _ ≤ (m j : ℝ≥0∞) * u := by
          rw [hu, ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hKN0) (Or.inl hKNt), mul_comm]; exact hw
    calc Q h A ≤ Q h (Afin ∪ ⋃ j ∈ S, A' j) := hmono _ _ _ hcov
      _ ≤ Q h Afin + Q h (⋃ j ∈ S, A' j) := hunion _ _ _
      _ ≤ K * u + ∑ j ∈ S, (m j : ℝ≥0∞) * u :=
          add_le_add (hfinK Afin hinv hfa) ((Q_iUnion_le Q hunion hempty h S A').trans (Finset.sum_le_sum key))
      _ = ((K + ∑ j ∈ S, m j : ℕ) : ℝ≥0∞) * u := by rw [← Finset.sum_mul]; push_cast; ring
      _ ≤ ((K * N : ℕ) : ℝ≥0∞) * u := by gcongr; omega
      _ = W h := by rw [hu]; exact ENNReal.mul_div_cancel hKN0 hKNt

end WaveTurbulence.GammaLow.FinalCount.Ghost

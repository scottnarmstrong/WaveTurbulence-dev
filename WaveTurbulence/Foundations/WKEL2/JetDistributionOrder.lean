/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetWordBound

/-!
# Top-order and lower-order coordinate distributions

This is the combinatorial separation used in TARGET (schappend11): a
distribution is constant, placing the whole word in one slot, or every
slot has strictly lower order.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- A constant distribution places the entire word in one input slot. -/
theorem jetDistrib_const (i : Fin 3) (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    ∀ {n : ℕ} (w : Fin n → JetLetter d),
      jetDistrib w (fun _ => i) F = Function.update F i (jetWordCLM (List.ofFn w) (F i))
  | 0, w => by simp only [jetDistrib, List.ofFn_zero, jetWordCLM_nil, Function.update_eq_self]
  | n + 1, w => by
      have htail : Fin.tail (fun _ : Fin (n + 1) => i) = (fun _ : Fin n => i) := rfl
      simp only [jetDistrib, htail]
      rw [jetDistrib_const i F (Fin.tail w)]
      rw [List.ofFn_succ, ← Fin.tail_def, jetWordCLM_cons]
      simp only [Function.update_self, Function.update_idem]

/-- A nonconstant distribution assigns fewer than n letters to each slot. -/
theorem card_jetDistrib_lt {n : ℕ} (σ : Fin n → Fin 3)
    (hσ : ∀ i : Fin 3, σ ≠ fun _ => i) (i : Fin 3) :
    (Finset.univ.filter (fun t => σ t = i)).card < n := by
  have hproper : Finset.univ.filter (fun t => σ t = i) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    apply hσ i
    funext t
    have ht : t ∈ Finset.univ.filter (fun t => σ t = i) := by rw [heq]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp ht).2
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hproper

/-- A single slot is controlled by any jet order at least its actual assigned letter count. -/
theorem weightedL2Norm_jetDistrib_le_of_count (s : ℝ) {m n : ℕ}
    (w : Fin n → JetLetter d) (σ : Fin n → Fin 3) (F : Fin 3 → 𝓢(Mom d, ℝ)) (i : Fin 3)
    (hc : (Finset.univ.filter (fun t => σ t = i)).card ≤ m) :
    weightedL2Norm s (jetDistrib w σ F i) ≤ ‖weightedJetCLM s m (F i)‖ := by
  obtain ⟨c, v, hvCount, hv⟩ := jetDistrib_eq_word w σ F i
  let q : JetIndex d m := ⟨⟨c, by omega⟩, v⟩
  have H := norm_le_pi_norm (weightedJetCLM s m (F i)) q
  rw [norm_weightedJetCLM_coordinate] at H
  rw [hv]
  exact H

/-- Every slot in a nonconstant distribution is bounded at the preceding jet order. -/
theorem weightedL2Norm_jetDistrib_low (s : ℝ) {n : ℕ}
    (w : Fin (n + 1) → JetLetter d) (σ : Fin (n + 1) → Fin 3)
    (hσ : ∀ i : Fin 3, σ ≠ fun _ => i) (F : Fin 3 → 𝓢(Mom d, ℝ)) (i : Fin 3) :
    weightedL2Norm s (jetDistrib w σ F i) ≤ ‖weightedJetCLM s n (F i)‖ := by
  apply weightedL2Norm_jetDistrib_le_of_count
  exact Nat.le_of_lt_succ (card_jetDistrib_lt σ hσ i)

end WaveTurbulence.WKEL2

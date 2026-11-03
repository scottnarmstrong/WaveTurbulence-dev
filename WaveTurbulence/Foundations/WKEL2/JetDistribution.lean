/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetIdentity

/-!
# Iterating the coordinate Leibniz and moment identities

Words and distributions retain every elementary term. Thus coincident
multi-index terms automatically carry their correct multiplicity.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Distribute an ordered coordinate word among the three inputs. -/
@[expose] def jetDistrib : {n : ℕ} → (Fin n → JetLetter d) → (Fin n → Fin 3) →
    (Fin 3 → 𝓢(Mom d, ℝ)) → Fin 3 → 𝓢(Mom d, ℝ)
  | 0, _, _, F => F
  | _ + 1, w, σ, F =>
      Function.update (jetDistrib (Fin.tail w) (Fin.tail σ) F) (σ 0)
        (jetLetterCLM (w 0) (jetDistrib (Fin.tail w) (Fin.tail σ) F (σ 0)))

/-- Product of the exact elementary signs and zero coefficients in a distribution. -/
@[expose] def jetSign : {n : ℕ} → (Fin n → JetLetter d) → Fin 4 → (Fin n → Fin 3) → ℝ
  | 0, _, _, _ => 1
  | _ + 1, w, j, σ =>
      jetCoefficient (w 0) j (σ 0) * jetSign (Fin.tail w) j (Fin.tail σ)

/-- Iterated TARGET (schappend6)–(schappend7), with all multiplicities retained. -/
theorem jetWordCLM_ktriple (hd : 2 ≤ d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    ∀ {n : ℕ} (w : Fin n → JetLetter d),
      jetWordCLM (List.ofFn w) (WKE.ktriple hd j F) =
        ∑ σ : Fin n → Fin 3, jetSign w j σ • WKE.ktriple hd j (jetDistrib w σ F)
  | 0, w => by simp [jetSign, jetDistrib, jetWordCLM]
  | n + 1, w => by
      rw [List.ofFn_succ, ← Fin.tail_def, jetWordCLM_cons, jetWordCLM_ktriple hd j F (Fin.tail w), map_sum]
      simp only [map_smul, jetLetterCLM_ktriple, Finset.smul_sum, smul_smul]
      rw [WKE.sum_fin_succ_fun, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro i _
      simp only [jetSign, jetDistrib, Fin.tail_cons, Fin.cons_zero]
      rw [mul_comm]

/-- Every distribution coefficient has absolute value at most one. -/
theorem abs_jetSign_le (j : Fin 4) : ∀ {n : ℕ} (w : Fin n → JetLetter d) (σ : Fin n → Fin 3),
    |jetSign w j σ| ≤ 1
  | 0, _, _ => by simp only [jetSign, abs_one, le_refl]
  | n + 1, w, σ => by
      rw [jetSign, abs_mul]
      exact (mul_le_mul (abs_jetCoefficient_le _ _ _) (abs_jetSign_le j _ _)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Each input receives exactly the letters assigned to its slot. -/
theorem jetDistrib_eq_word : ∀ {n : ℕ} (w : Fin n → JetLetter d) (σ : Fin n → Fin 3)
    (F : Fin 3 → 𝓢(Mom d, ℝ)) (i : Fin 3),
    ∃ (c : ℕ) (v : Fin c → JetLetter d),
      c = (Finset.univ.filter (fun t => σ t = i)).card ∧
        jetDistrib w σ F i = jetWordCLM (List.ofFn v) (F i)
  | 0, _, _, F, i => ⟨0, Fin.elim0, by simp, rfl⟩
  | n + 1, w, σ, F, i => by
      obtain ⟨c, v, hc, hv⟩ := jetDistrib_eq_word (Fin.tail w) (Fin.tail σ) F i
      by_cases hi : σ 0 = i
      · refine ⟨c + 1, Fin.cons (w 0) v, ?_, ?_⟩
        · rw [WKE.card_filter_fin_succ, ite_eq_left hi, hc]
          omega
        · simp only [jetDistrib]
          rw [← hi, Function.update_self, hi, hv, List.ofFn_cons, jetWordCLM_cons]
      · refine ⟨c, v, ?_, ?_⟩
        · rw [WKE.card_filter_fin_succ, ite_eq_right hi, hc, zero_add]
        · simp only [jetDistrib]
          rw [Function.update_of_ne (Ne.symm hi), hv]

end WaveTurbulence.WKEL2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetDistribution
public import WaveTurbulence.Foundations.WKEL2.JetEstimates

/-!
# Uniform finite-jet collision bounds

TARGET Appendix C, L2526: the same trilinear estimate holds in every finite
weighted moment and derivative space. Ordered distributions give the explicit
harmless factor 3^m, retaining every Leibniz multiplicity.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- A distributed input uses no more than the original number of coordinate letters. -/
theorem weightedL2Norm_jetDistrib_le (s : ℝ) {m n : ℕ} (hnm : n ≤ m)
    (w : Fin n → JetLetter d) (σ : Fin n → Fin 3) (F : Fin 3 → 𝓢(Mom d, ℝ)) (i : Fin 3) :
    weightedL2Norm s (jetDistrib w σ F i) ≤ ‖weightedJetCLM s m (F i)‖ := by
  obtain ⟨c, v, hc, hv⟩ := jetDistrib_eq_word w σ F i
  have hcn : c ≤ n := by
    rw [hc]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun t : Fin n => σ t = i) Finset.univ)
  let q : JetIndex d m := ⟨⟨c, by omega⟩, v⟩
  have H := norm_le_pi_norm (weightedJetCLM s m (F i)) q
  rw [norm_weightedJetCLM_coordinate] at H
  rw [hv]
  exact H

/-- A single coordinate word obeys Theorem 7 with at most 3^n distributed terms. -/
theorem exists_jetWord_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℕ), n ≤ m → ∀ (w : Fin n → JetLetter d)
      (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)),
      weightedL2Norm s (jetWordCLM (List.ofFn w) (WKE.ktriple (by omega) j F)) ≤
        (3 : ℝ) ^ n * (C * ‖weightedJetCLM s m (F 0)‖ *
          ‖weightedJetCLM s m (F 1)‖ * ‖weightedJetCLM s m (F 2)‖) := by
  obtain ⟨C, hC, hb⟩ := exists_collisionTerm_bound hd s hs
  refine ⟨C, hC, fun m n hnm w j F => ?_⟩
  let N := fun i : Fin 3 => ‖weightedJetCLM s m (F i)‖
  have H : ∀ σ : Fin n → Fin 3,
      ‖weightedToL2CLM s (WKE.ktriple (by omega) j (jetDistrib w σ F))‖ ≤
        C * N 0 * N 1 * N 2 := by
    intro σ
    let G := jetDistrib w σ F
    have HG := (hb j (G 0) (G 1) (G 2) (G 0).continuous.measurable
      (G 1).continuous.measurable (G 2).continuous.measurable
      (memLp_weighted_schwartz s _) (memLp_weighted_schwartz s _)
      (memLp_weighted_schwartz s _)).2
    have hG : ∀ i, weightedL2Norm s (G i) ≤ N i :=
      fun i => weightedL2Norm_jetDistrib_le s hnm w σ F i
    rw [norm_weightedToL2CLM, WKE.coe_ktriple]
    apply HG.trans
    calc
      _ ≤ C * N 0 * weightedL2Norm s (G 1) * weightedL2Norm s (G 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG 0) hC)
            (weightedL2Norm_nonneg _ _)) (weightedL2Norm_nonneg _ _)
      _ ≤ C * N 0 * N 1 * weightedL2Norm s (G 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG 1)
          (mul_nonneg hC (norm_nonneg _))) (weightedL2Norm_nonneg _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hG 2)
        (mul_nonneg (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _))
  rw [← norm_weightedToL2CLM, jetWordCLM_ktriple, map_sum]
  calc
    _ ≤ ∑ σ : Fin n → Fin 3,
        ‖weightedToL2CLM s (jetSign w j σ • WKE.ktriple (by omega) j (jetDistrib w σ F))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Fin n → Fin 3, C * N 0 * N 1 * N 2 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (abs_jetSign_le j w σ) (norm_nonneg _)).trans
        (by simpa only [one_mul] using H σ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, N]

/-- The finite supremum weighted jet norm is trilinearly bounded at every order. -/
theorem exists_weightedJet_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)),
      ‖weightedJetCLM s m (WKE.ktriple (by omega) j F)‖ ≤
        C * ‖weightedJetCLM s m (F 0)‖ * ‖weightedJetCLM s m (F 1)‖ *
          ‖weightedJetCLM s m (F 2)‖ := by
  obtain ⟨C, hC, hb⟩ := exists_jetWord_bound hd s hs
  refine ⟨3 ^ m * C, by positivity, fun j F => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro q
  rw [norm_weightedJetCLM_coordinate]
  have H := hb m q.1 (Nat.le_of_lt_succ q.1.isLt) q.2 j F
  apply H.trans
  calc
    _ ≤ 3 ^ m * (C * ‖weightedJetCLM s m (F 0)‖ * ‖weightedJetCLM s m (F 1)‖ *
        ‖weightedJetCLM s m (F 2)‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        (Nat.le_of_lt_succ q.1.isLt)) (by positivity)
    _ = _ := by ring

end WaveTurbulence.WKEL2

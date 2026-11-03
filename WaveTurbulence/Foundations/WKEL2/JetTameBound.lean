/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetDistributionOrder

/-!
# The tame top-order collision estimate

TARGET (schappend11), L2521–L2524. Only the three constant distributions
contain a highest-order input. Their coefficient uses the base weighted L²
norm squared; all remaining distributions use the preceding jet norm.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The top-order weighted estimate has a base-norm coefficient independent of the order. -/
theorem exists_jetWord_tame_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : Fin (n + 1) → JetLetter d)
      (j : Fin 4) (f : 𝓢(Mom d, ℝ)),
      weightedL2Norm s (jetWordCLM (List.ofFn w) (WKE.ktriple (by omega) j (fun _ => f))) ≤
        3 * C * weightedL2Norm s f ^ 2 * weightedL2Norm s (jetWordCLM (List.ofFn w) f) +
          (3 : ℝ) ^ (n + 1) * C * ‖weightedJetCLM s n f‖ ^ 3 := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_collisionTerm_bound hd s hs
  refine ⟨C, hC, fun n w j f => ?_⟩
  let F : Fin 3 → 𝓢(Mom d, ℝ) := fun _ => f
  let D := C * weightedL2Norm s f ^ 2 * weightedL2Norm s (jetWordCLM (List.ofFn w) f)
  let L := C * ‖weightedJetCLM s n f‖ ^ 3
  let I := fun σ : Fin (n + 1) → Fin 3 => ∑ i : Fin 3, if σ = (fun _ => i) then D else 0
  have hD : 0 ≤ D :=
    mul_nonneg (mul_nonneg hC (sq_nonneg _)) (weightedL2Norm_nonneg _ _)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hI : ∀ σ, 0 ≤ I σ := fun σ => Finset.sum_nonneg fun i _ => by split <;> positivity
  have hTerm : ∀ σ : Fin (n + 1) → Fin 3,
      ‖weightedToL2CLM s (WKE.ktriple (by omega) j (jetDistrib w σ F))‖ ≤ I σ + L := by
    intro σ
    let G := jetDistrib w σ F
    have H := (hb j (G 0) (G 1) (G 2) (G 0).continuous.measurable
      (G 1).continuous.measurable (G 2).continuous.measurable
      (memLp_weighted_schwartz s _) (memLp_weighted_schwartz s _)
      (memLp_weighted_schwartz s _)).2
    rw [norm_weightedToL2CLM, WKE.coe_ktriple]
    by_cases hconst : ∃ i : Fin 3, σ = fun _ => i
    · obtain ⟨i, rfl⟩ := hconst
      have hGD : C * weightedL2Norm s (G 0) * weightedL2Norm s (G 1) *
          weightedL2Norm s (G 2) = D := by
        dsimp only [G]
        rw [jetDistrib_const]
        fin_cases i <;> dsimp [F, Function.update, D] <;> ring
      have hi : D ≤ I (fun _ => i) := by
        have HH := Finset.single_le_sum (s := Finset.univ)
          (f := fun l : Fin 3 => if (fun _ : Fin (n + 1) => i) = (fun _ => l) then D else 0)
          (fun l _ => by split <;> positivity) (Finset.mem_univ i)
        simpa only [ite_true] using HH
      exact (H.trans_eq hGD).trans (hi.trans (le_add_of_nonneg_right hL))
    · have hσ : ∀ i : Fin 3, σ ≠ fun _ => i := fun i hi => hconst ⟨i, hi⟩
      have hG : ∀ i, weightedL2Norm s (G i) ≤ ‖weightedJetCLM s n f‖ := by
        intro i
        exact weightedL2Norm_jetDistrib_low s w σ hσ F i
      have HB : C * weightedL2Norm s (G 0) * weightedL2Norm s (G 1) *
          weightedL2Norm s (G 2) ≤ L := by
        calc
          _ ≤ C * ‖weightedJetCLM s n f‖ * weightedL2Norm s (G 1) * weightedL2Norm s (G 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG 0) hC)
                (weightedL2Norm_nonneg _ _)) (weightedL2Norm_nonneg _ _)
          _ ≤ C * ‖weightedJetCLM s n f‖ * ‖weightedJetCLM s n f‖ * weightedL2Norm s (G 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG 1)
              (mul_nonneg hC (norm_nonneg _))) (weightedL2Norm_nonneg _ _)
          _ ≤ C * ‖weightedJetCLM s n f‖ * ‖weightedJetCLM s n f‖ * ‖weightedJetCLM s n f‖ :=
            mul_le_mul_of_nonneg_left (hG 2) (by positivity)
          _ = L := by dsimp only [L]; ring
      exact (H.trans HB).trans (le_add_of_nonneg_left (hI σ))
  rw [← norm_weightedToL2CLM, jetWordCLM_ktriple, map_sum]
  calc
    _ ≤ ∑ σ : Fin (n + 1) → Fin 3,
        ‖weightedToL2CLM s (jetSign w j σ • WKE.ktriple (by omega) j (jetDistrib w σ F))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ σ : Fin (n + 1) → Fin 3, (I σ + L) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (abs_jetSign_le j w σ) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hTerm σ)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      dsimp only [I]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [D, L]
      ring

end WaveTurbulence.WKEL2

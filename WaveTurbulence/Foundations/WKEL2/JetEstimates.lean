/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetIdentity
public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevCoordinates
public import WaveTurbulence.Foundations.WKEL2.Trilinear

/-!
# Weighted derivative and moment bounds from Theorem 7
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Theorem 7 and the exact coordinate identity control every first derivative and moment. -/
theorem exists_jetLetter_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : JetLetter d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)),
      weightedL2Norm s (jetLetterCLM a (WKE.ktriple (by omega) j F)) ≤
        ∑ i : Fin 3,
          C * weightedL2Norm s (Function.update F i (jetLetterCLM a (F i)) 0) *
            weightedL2Norm s (Function.update F i (jetLetterCLM a (F i)) 1) *
            weightedL2Norm s (Function.update F i (jetLetterCLM a (F i)) 2) := by
  obtain ⟨C, hC, hb⟩ := exists_collisionTerm_bound hd s hs
  refine ⟨C, hC, fun a j F => ?_⟩
  let G := fun i : Fin 3 => Function.update F i (jetLetterCLM a (F i))
  have H : ∀ i : Fin 3,
      ‖weightedToL2CLM s (WKE.ktriple (by omega) j (G i))‖ ≤
        C * weightedL2Norm s (G i 0) * weightedL2Norm s (G i 1) * weightedL2Norm s (G i 2) := by
    intro i
    rw [norm_weightedToL2CLM, WKE.coe_ktriple]
    exact (hb j (G i 0) (G i 1) (G i 2) (G i 0).continuous.measurable
      (G i 1).continuous.measurable (G i 2).continuous.measurable
      (memLp_weighted_schwartz s _) (memLp_weighted_schwartz s _)
      (memLp_weighted_schwartz s _)).2
  rw [← norm_weightedToL2CLM, jetLetterCLM_ktriple, map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right (abs_jetCoefficient_le a j i) (norm_nonneg _)).trans
  simpa only [one_mul, G] using H i

end WaveTurbulence.WKEL2

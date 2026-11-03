/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedJets
public import WaveTurbulence.Foundations.WKE.IteratedLeibniz

/-!
# Coordinate Leibniz and moment identities for the collision jets

TARGET (schappend6)–(schappend7), L2508–L2511. The gain moment identity
has signs (+,-,+); each loss term carries its moment in the outer slot.
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Exact coefficient of a coordinate letter distributed to an input slot. -/
@[expose] def jetCoefficient (a : JetLetter d) (j : Fin 4) (i : Fin 3) : ℝ :=
  match a with
  | .inr _ => 1
  | .inl _ => if j = 0 then (if i = 1 then -1 else 1)
      else if j.val = i.val + 1 then 1 else 0

/-- Every elementary coefficient is bounded in absolute value by one. -/
theorem abs_jetCoefficient_le (a : JetLetter d) (j : Fin 4) (i : Fin 3) :
    |jetCoefficient a j i| ≤ 1 := by
  cases a with
  | inl a => fin_cases j <;> fin_cases i <;> norm_num [jetCoefficient]
  | inr a => simp only [jetCoefficient, abs_one, le_refl]

/-- Schwartz coordinate Leibniz and weight identities in a uniform finite-sum form. -/
theorem jetLetterCLM_ktriple (hd : 2 ≤ d) (a : JetLetter d) (j : Fin 4)
    (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    jetLetterCLM a (WKE.ktriple hd j F) =
      ∑ i : Fin 3, jetCoefficient a j i •
        WKE.ktriple hd j (Function.update F i (jetLetterCLM a (F i))) := by
  cases a with
  | inr i =>
      simpa only [jetLetterCLM, jetCoefficient, one_smul, LineDeriv.lineDerivOpCLM_apply] using
        WKE.lineDerivOp_ktriple hd j F (EuclideanSpace.single i (1 : ℝ))
  | inl i =>
      fin_cases j
      · obtain ⟨C, H⟩ := collisionInputs_of_schwartz (F 0) (F 1) (F 2)
          (show 2 * (d : ℝ) < (2 * d + 1) + 1 by linarith)
        ext k
        have hw := WKE.weight_collisionTerm_zero hd
          (show 2 * (d : ℝ) < 2 * d + 1 by linarith)
          H.cont₁ H.cont₂ H.cont₃ H.decay₁ H.decay₂ H.decay₃ (EuclideanSpace.proj i) k
        simpa [jetLetterCLM, coordinateWeightCLM_apply, coe_coordinateWeightCLM, WKE.coe_ktriple,
          jetCoefficient, Fin.sum_univ_three, Function.update, sub_eq_add_neg] using hw
      · ext k
        simpa [jetLetterCLM, coordinateWeightCLM_apply, coe_coordinateWeightCLM, WKE.coe_ktriple,
          jetCoefficient, Fin.sum_univ_three, Function.update] using
          WKE.weight_collisionTerm_one (φ₁ := F 0) (φ₂ := F 1) (φ₃ := F 2)
            (EuclideanSpace.proj i) k
      · ext k
        simpa [jetLetterCLM, coordinateWeightCLM_apply, coe_coordinateWeightCLM, WKE.coe_ktriple,
          jetCoefficient, Fin.sum_univ_three, Function.update] using
          WKE.weight_collisionTerm_two (φ₁ := F 0) (φ₂ := F 1) (φ₃ := F 2)
            (EuclideanSpace.proj i) k
      · ext k
        simpa [jetLetterCLM, coordinateWeightCLM_apply, coe_coordinateWeightCLM, WKE.coe_ktriple,
          jetCoefficient, Fin.sum_univ_three, Function.update] using
          WKE.weight_collisionTerm_three (φ₁ := F 0) (φ₂ := F 1) (φ₃ := F 2)
            (EuclideanSpace.proj i) k

end WaveTurbulence.WKEL2

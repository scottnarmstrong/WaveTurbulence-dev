/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ReplacementMass
public import WaveTurbulence.Foundations.Incoh.ReplacementPenalty
public import WaveTurbulence.Foundations.Incoh.ProductDecay

/-!
# Product decay with finitely many replaced links

TARGET (incohproof18), (incohproof27). This retains the incoherence gain
on every link and charges an explicit power for each trivial replacement.
The same threshold works for all replacement sets and all link counts.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal replacement-mass product has only an explicit cardinality-dependent power loss. -/
theorem exists_replacedLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ J : Finset (Fin n), (∏ i, replacedLinkMass L γ δ Q J i) ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n * C₂ ^ incoherenceCount Q *
            L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) *
              L ^ ((2 * γ + incoherenceExponent d γ - η) * J.card)) := by
  obtain ⟨C, hC, hb⟩ := exists_oneLink_decay d hd
  let C₀ : ℝ := C + 5 ^ (2 * d) + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hCC₀ : C ≤ C₀ := by dsimp [C₀]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (2 * d)]
  have htriv : (5 : ℝ) ^ (2 * d) ≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨C₂, L₀, hC₂, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨C₂, L₀, hC₂, hL₀, ?_⟩
  intro L hL n Q hspan J
  classical
  have hL₁ := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hL₁
  have hbase : 0 ≤ kineticLinkScale d γ δ L := by unfold kineticLinkScale; positivity
  let W : ℝ := C₂ * L ^ (-(incoherenceExponent d γ - η))
  let P : ℝ := L ^ (2 * γ + (incoherenceExponent d γ - η))
  have hW : 0 ≤ W := mul_nonneg (zero_le_one.trans hC₂) (Real.rpow_nonneg hLp.le _)
  have hP : 0 ≤ P := Real.rpow_nonneg hLp.le _
  have hnormal (i : Fin n) : layerLinkMass L (δ * L ^ (2 * γ)) (Q i) ≤
      ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) * if (Q i).IsIncoherent then W else 1) := by
    have h := hb L hL (Q i) (hspan i)
    by_cases hi : (Q i).IsIncoherent
    · rw [ite_eq_left hi]
      apply (h.2 hi).trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (C * kineticLinkScale d γ δ L) * W := by dsimp [W]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hbase) hW
    · rw [ite_eq_right hi, mul_one]
      exact h.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC₀ hbase))
  have hbound (i : Fin n) : replacedLinkMass L γ δ Q J i ≤
      ENNReal.ofReal (((C₀ * kineticLinkScale d γ δ L) * if (Q i).IsIncoherent then W else 1) *
        if i ∈ J then P else 1) := by
    by_cases hi : i ∈ J
    · rw [replacedLinkMass, ite_eq_left hi, ite_eq_left hi]
      apply ENNReal.ofReal_le_ofReal
      exact trivial_link_le_weighted_penalty hL₁ hδ hδ₁ (sub_pos.mpr hηg).le htriv hC₂ _
    · rw [replacedLinkMass, ite_eq_right hi, ite_eq_right hi, mul_one]
      exact hnormal i
  calc
    _ ≤ ∏ i, ENNReal.ofReal (((C₀ * kineticLinkScale d γ δ L) * if (Q i).IsIncoherent then W else 1) *
        if i ∈ J then P else 1) := Finset.prod_le_prod fun i _ => hbound i
    _ = ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n * W ^ incoherenceCount Q * P ^ J.card) := by
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rw [Finset.prod_mul_distrib, prod_link_weights, Finset.prod_ite_mem_eq, Finset.prod_const]
      · intro i _
        apply mul_nonneg
        · exact mul_nonneg (mul_nonneg hC₀.le hbase) (by split_ifs <;> positivity)
        · split_ifs <;> positivity
    _ = _ := by
      dsimp only [W, P]
      rw [mul_pow C₂ (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← Real.rpow_natCast (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← Real.rpow_mul hLp.le, ← Real.rpow_natCast (L ^ (2 * γ + (incoherenceExponent d γ - η))) J.card,
        ← Real.rpow_mul hLp.le]
      rw [show 2 * γ + (incoherenceExponent d γ - η) = 2 * γ + incoherenceExponent d γ - η by ring]
      congr 1
      ring

end WaveTurbulence.Incoh

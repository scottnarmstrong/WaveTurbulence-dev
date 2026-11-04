/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.OneLinkDecay
public import WaveTurbulence.Foundations.Incoh.ProductMass

/-!
# Decay of the product over all localized links

TARGET (incohproof16). Each incoherent link contributes its proved gain;
the time-order domain is dominated by the actual product of layer boxes.
The threshold is uniform in both the number of links and their parameters.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Multiplying the incoherence flags counts exactly the incoherent links. -/
theorem prod_link_weights {d n : ℕ} (Q : Fin n → LayerLink d) (A B : ℝ)
    [DecidablePred (fun i => (Q i).IsIncoherent)] :
    (∏ i, A * if (Q i).IsIncoherent then B else 1) = A ^ n * B ^ incoherenceCount Q := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one,
    incoherenceCount]
  congr 2
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- TARGET (incohproof16), with exact link count and incoherence count, before absorbing `C₂^g`. -/
theorem exists_linkMassProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        (∏ i, layerLinkMass L (δ * L ^ (2 * γ)) (Q i)) ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n * C₂ ^ incoherenceCount Q *
            L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_oneLink_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨C₂, L₀, hC₂, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨C₂, L₀, hC₂, hL₀, ?_⟩
  intro L hL n Q hspan
  classical
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hbase : 0 ≤ C₀ * kineticLinkScale d γ δ L := by unfold kineticLinkScale; positivity
  let W : ℝ := C₂ * L ^ (-(incoherenceExponent d γ - η))
  have hW : 0 ≤ W := mul_nonneg (zero_le_one.trans hC₂) (Real.rpow_nonneg hLp.le _)
  have hbound (i : Fin n) : layerLinkMass L (δ * L ^ (2 * γ)) (Q i) ≤
      ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) * if (Q i).IsIncoherent then W else 1) := by
    have h := hb L hL (Q i) (hspan i)
    by_cases hi : (Q i).IsIncoherent
    · rw [ite_eq_left hi]
      convert h.2 hi using 1
      congr 1
      dsimp only [W]
      ring
    · rw [ite_eq_right hi, mul_one]
      exact h.1
  calc
    _ ≤ ∏ i, ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) * if (Q i).IsIncoherent then W else 1) :=
      Finset.prod_le_prod fun i _ => hbound i
    _ = ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n * W ^ incoherenceCount Q) := by
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rw [prod_link_weights]
      · intro i _
        exact mul_nonneg hbase (by split_ifs <;> positivity)
    _ = _ := by
      dsimp only [W]
      rw [mul_pow C₂ (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← mul_assoc, ← Real.rpow_natCast (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← Real.rpow_mul hLp.le]

/-- TARGET (incohproof16), for the actual oscillatory product integral. -/
theorem exists_linkProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ‖∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n * C₂ ^ incoherenceCount Q *
            L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_linkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨C₂, L₀, hC₂, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨C₂, L₀, hC₂, hL₀, ?_⟩
  intro L hL n Q hspan I hI
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  exact (enorm_linkProduct_integral_le hLp γ δ Q hI).trans (hb L hL n Q hspan)

end WaveTurbulence.Incoh

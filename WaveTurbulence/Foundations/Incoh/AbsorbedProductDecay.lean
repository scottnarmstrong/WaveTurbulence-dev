/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ProductDecay

/-!
# Product decay after absorbing the secondary constant

TARGET (incohproof16)–(incohproof18). A single large-box threshold
absorbs `C₂^g` by `L^(ηg)` for every link count, preserving the dimensional
base constant selected before the coupling and layer range.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The full product bound with all secondary constants absorbed in one `ηg` loss. -/
theorem exists_absorbed_linkMassProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        (∏ i, layerLinkMass L (δ * L ^ (2 * γ)) (Q i)) ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_linkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨C₂, L₁, hC₂, hL₁, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₂, hL₂, ha⟩ := exists_counted_constant_absorption_threshold (zero_le_one.trans hC₂) hη
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLp := zero_lt_one.trans_le (hL₁.trans hLa)
  apply (hb L hLa n Q hspan).trans
  apply ENNReal.ofReal_le_ofReal
  have hbase : 0 ≤ (C₀ * kineticLinkScale d γ δ L) ^ n := by unfold kineticLinkScale; positivity
  calc
    _ ≤ (C₀ * kineticLinkScale d γ δ L) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha L hLb _) hbase) (Real.rpow_nonneg hLp.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hLp]
      congr 2
      ring

/-- The absorbed bound for the oscillatory product integral. -/
theorem exists_absorbed_linkProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ‖∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_linkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hI
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  exact (enorm_linkProduct_integral_le hLp γ δ Q hI).trans (hb L hL n Q hspan)

/-- The absolute-integral form needed for root-density L¹ estimates. -/
theorem exists_absolute_linkProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        (∫⁻ t in I, ‖∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ) ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_linkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hI
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  exact (lintegral_linkProduct_enorm_le hLp γ δ Q hI).trans (hb L hL n Q hspan)

end WaveTurbulence.Incoh

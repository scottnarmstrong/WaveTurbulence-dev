/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ReplacementDecay

/-!
# Uniform decay after a bounded number of replacements

TARGET (incohproof18), (incohproof27). Secondary constants are absorbed
uniformly in the incoherence count; at most `k` replacements cost `L^(dk)`.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- A single threshold controls every link family and every replacement set of cardinality at most `k`. -/
theorem exists_absorbed_replacedLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        (∏ i, replacedLinkMass L γ δ Q J i) ≤
          ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_replacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨C₂, L₁, hC₂, hL₁, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₂, hL₂, ha⟩ := exists_counted_constant_absorption_threshold (zero_le_one.trans hC₂) hη
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan k J hJ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLone := hL₁.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hpen := replacement_loss_budget hd hγ.2.le hη.le hJ
  have hbase : 0 ≤ (C₀ * kineticLinkScale d γ δ L) ^ n := by unfold kineticLinkScale; positivity
  apply (hb L hLa n Q hspan J).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C₀ * kineticLinkScale d γ δ L) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) *
          L ^ ((2 * γ + incoherenceExponent d γ - η) * J.card) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha L hLb _) hbase) (Real.rpow_nonneg hLp.le _))
        (Real.rpow_nonneg hLp.le _)
    _ ≤ (C₀ * kineticLinkScale d γ δ L) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) * L ^ ((d : ℝ) * k) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLone hpen) (by positivity)
    _ = _ := by
      congr 1
      rw [mul_assoc, ← Real.rpow_add hLp]
      congr 2
      ring

end WaveTurbulence.Incoh

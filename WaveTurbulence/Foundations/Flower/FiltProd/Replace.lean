/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Mass

/-! # D5b-2 FILT-PROD: replacements (twins of `ReplacementMass`, `ReplacementDecay`, `AbsorbedReplacementDecay`,
`NormalizedReplacementDecay`). The replaced link costs the trivial bound `K (5L)^{2d}` (D5a: `‖φ‖ ≤ K`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc

/-- Twin of `replacedLinkMass`: selected links pay the trivial bound `K (5L)^{2d}`. -/
def replacedLinkMassFilt {d n : ℕ} (K L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (J : Finset (Fin n)) (i : Fin n) : ℝ≥0∞ :=
  if i ∈ J then ENNReal.ofReal (K * (5 * L) ^ (2 * d)) else
    filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i)

theorem exists_replacedFiltLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ J : Finset (Fin n), (∏ i, replacedLinkMassFilt K L γ δ Q φ J i) ≤
          ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n * C₂ ^ incoherenceCount Q *
            L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) *
              L ^ ((2 * γ + incoherenceExponent d γ - η) * J.card)) := by
  obtain ⟨C, hC, hb⟩ := exists_filtOneLink_decay d hd
  let C₀ : ℝ := C + 5 ^ (2 * d) + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hCC₀ : C ≤ C₀ := by dsimp [C₀]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (2 * d)]
  have htriv : (5 : ℝ) ^ (2 * d) ≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨C₂, L₀, hC₂, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨C₂, L₀, hC₂, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ J
  classical
  have hL₁ := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hL₁
  have hbase : 0 ≤ kineticLinkScale d γ δ L := by unfold kineticLinkScale; positivity
  let W : ℝ := C₂ * L ^ (-(incoherenceExponent d γ - η))
  let P : ℝ := L ^ (2 * γ + (incoherenceExponent d γ - η))
  have hW : 0 ≤ W := mul_nonneg (zero_le_one.trans hC₂) (Real.rpow_nonneg hLp.le _)
  have hP : 0 ≤ P := Real.rpow_nonneg hLp.le _
  have hnormal (i : Fin n) : filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i) ≤
      ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) * if (Q i).IsIncoherent then W else 1) := by
    have h := hb L hL (Q i) (hspan i) K (φ i) (hφ i)
    by_cases hi : (Q i).IsIncoherent
    · rw [ite_eq_left hi]
      apply (h.2 hi).trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = K * ((C * kineticLinkScale d γ δ L) * W) := by dsimp [W]; ring
        _ ≤ K * ((C₀ * kineticLinkScale d γ δ L) * W) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hbase) hW) hK
        _ = _ := by ring
    · rw [ite_eq_right hi, mul_one]
      exact h.1.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCC₀ hbase) hK))
  have hbound (i : Fin n) : replacedLinkMassFilt K L γ δ Q φ J i ≤
      ENNReal.ofReal (((K * (C₀ * kineticLinkScale d γ δ L)) * if (Q i).IsIncoherent then W else 1) *
        if i ∈ J then P else 1) := by
    by_cases hi : i ∈ J
    · rw [replacedLinkMassFilt, ite_eq_left hi, ite_eq_left hi]
      apply ENNReal.ofReal_le_ofReal
      have := trivial_link_le_weighted_penalty (d := d) (γ := γ) hL₁ hδ hδ₁ (sub_pos.mpr hηg).le htriv hC₂
        ((Q i).IsIncoherent)
      calc K * (5 * L) ^ (2 * d) ≤ K * ((C₀ * kineticLinkScale d γ δ L) *
            (if (Q i).IsIncoherent then C₂ * L ^ (-(incoherenceExponent d γ - η)) else 1) *
              L ^ (2 * γ + (incoherenceExponent d γ - η))) := mul_le_mul_of_nonneg_left this hK
        _ = _ := by dsimp only [W, P]; ring
    · rw [replacedLinkMassFilt, ite_eq_right hi, ite_eq_right hi, mul_one]
      exact hnormal i
  calc
    _ ≤ ∏ i, ENNReal.ofReal (((K * (C₀ * kineticLinkScale d γ δ L)) * if (Q i).IsIncoherent then W else 1) *
        if i ∈ J then P else 1) := Finset.prod_le_prod fun i _ => hbound i
    _ = ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n * W ^ incoherenceCount Q * P ^ J.card) := by
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rw [Finset.prod_mul_distrib, prod_link_weights, Finset.prod_ite_mem_eq, Finset.prod_const]
      · intro i _
        apply mul_nonneg
        · exact mul_nonneg (mul_nonneg hK (mul_nonneg hC₀.le hbase)) (by split_ifs <;> positivity)
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

theorem exists_absorbed_replacedFiltLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        (∏ i, replacedLinkMassFilt K L γ δ Q φ J i) ≤
          ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_replacedFiltLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨C₂, L₁, hC₂, hL₁, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₂, hL₂, ha⟩ := exists_counted_constant_absorption_threshold (zero_le_one.trans hC₂) hη
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan K hK φ hφ k J hJ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLone := hL₁.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hpen := replacement_loss_budget hd hγ.2.le hη.le hJ
  have hbase : 0 ≤ (K * (C₀ * kineticLinkScale d γ δ L)) ^ n := by unfold kineticLinkScale; positivity
  apply (hb L hLa n Q hspan K hK φ hφ J).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (K * (C₀ * kineticLinkScale d γ δ L)) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) *
          L ^ ((2 * γ + incoherenceExponent d γ - η) * J.card) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha L hLb _) hbase) (Real.rpow_nonneg hLp.le _))
        (Real.rpow_nonneg hLp.le _)
    _ ≤ (K * (C₀ * kineticLinkScale d γ δ L)) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) * L ^ ((d : ℝ) * k) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLone hpen) (by positivity)
    _ = _ := by
      congr 1
      rw [mul_assoc, ← Real.rpow_add hLp]
      congr 2
      ring

/-- Twin of `normalizedReplacedLinkMass`. -/
def normalizedReplacedLinkMassFilt {d n : ℕ} (K L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
    ∏ i, replacedLinkMassFilt K L γ δ Q φ J i

theorem exists_normalizedReplacedFiltLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        normalizedReplacedLinkMassFilt K L γ δ Q φ J ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_replacedFiltLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ k J hJ
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  unfold normalizedReplacedLinkMassFilt
  apply (mul_le_mul' le_rfl (hb L hL n Q hspan K hK φ hφ k J hJ)).trans
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hKC : 0 ≤ K * C₀ := mul_nonneg hK hC₀.le
  have hcs := coupling_scale_le (d := d) (n := n) hLp hδ hKC γ
  calc
    _ = (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (K * C₀ * kineticLinkScale d γ δ L) ^ n) *
        L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) * L ^ ((d : ℝ) * k) := by
      rw [mul_assoc K C₀]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcs
        (Real.rpow_nonneg hLp.le _)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Flower.FiltProd

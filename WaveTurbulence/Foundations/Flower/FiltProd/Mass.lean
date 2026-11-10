/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Link
public import WaveTurbulence.Foundations.Flower.FiltLink.Decay
public import WaveTurbulence.Foundations.Incoh.AbsorbedProductDecay
public import WaveTurbulence.Foundations.Incoh.NormalizedReplacementDecay

/-! # D5b-2 FILT-PROD: masses and products (twins of `ProductMass`, `ProductDecay`, `AbsorbedProductDecay`,
`ReplacementMass`, `ReplacementDecay`, `AbsorbedReplacementDecay`, `NormalizedReplacementDecay`)

Convention: link `i` carries `φ i`, and the decay hypothesis is `hφ : ∀ i, PresentedMult L K (φ i)` (D5a (14.2)) with
`0 ≤ K`; the constants `C₀, C₂, L₀` do not depend on `K`, and the bound is main's with `C₀` replaced by `K * C₀`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc

/-- A `K`-presented multiplier is bounded by `K`. -/
theorem PresentedMult.norm_le {L K : ℝ} {φ : ℝ → ℂ} (h : PresentedMult L K φ) (hL : 0 ≤ L) (hK : 0 ≤ K) (u : ℝ) :
    ‖φ u‖ ≤ K := by
  obtain ⟨Ω, m, μ, hμ, G, T, hG, hT, hi, he, hk⟩ := h
  rw [he u]
  have h1 : ‖∫ ω, G ω * WeylSums.e (T ω * u) ∂μ‖ ≤ ∫ ω, ‖G ω‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_mul, WeylSums.norm_e, mul_one]
  refine h1.trans ?_
  have h2 : ENNReal.ofReal (∫ ω, ‖G ω‖ ∂μ) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hi]
    refine le_trans (lintegral_mono fun ω => ?_) hk
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + L * |T ω|) ^ 2) := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg hL (abs_nonneg (T ω))]
    exact le_mul_of_one_le_right zero_le this
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp h2

/-! ### `ProductMass` -/

/-- The filtered link mass is the real absolute integral. -/
theorem filtLayerLinkMass_eq_ofReal_integral {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) :
    filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ =
      ENNReal.ofReal (∫ t in linkBox Q, ‖filtLinkTimeFactor L γ δ Q φ t‖) := by
  rw [filtLayerLinkMass_eq]
  simp_rw [← ofReal_norm]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_filtLinkTimeFactor hL γ δ Q φ).norm
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm

theorem lintegral_linkProduct_enorm_leFilt {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    (∫⁻ t in I, ‖∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖ₑ) ≤
      ∏ i, filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i) := by
  have hi := (integrableOn_linkProductFilt hL γ δ Q φ hI).norm
  have heq : (∫⁻ t in I, ‖∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖ₑ) =
      ENNReal.ofReal (∫ t in I, ∏ i, ‖filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖) := by
    simp_rw [← ofReal_norm, norm_prod]
    exact (ofReal_integral_eq_lintegral_ofReal (by simpa only [norm_prod] using hi)
      (Filter.Eventually.of_forall fun t => Finset.prod_nonneg fun _ _ => norm_nonneg _)).symm
  rw [heq]
  apply (ENNReal.ofReal_le_ofReal (setIntegral_pi_product_norm_le hI
    (fun i => integrableOn_filtLinkTimeFactor hL γ δ (Q i) (φ i)))).trans_eq
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  exact Finset.prod_congr rfl fun i _ => (filtLayerLinkMass_eq_ofReal_integral hL γ δ (Q i) (φ i)).symm

/-! ### `ProductDecay` -/

theorem exists_filtLinkMassProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        (∏ i, filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i)) ≤
          ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n * C₂ ^ incoherenceCount Q *
            L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_filtOneLink_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨C₂, L₀, hC₂, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨C₂, L₀, hC₂, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ
  classical
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hbase : 0 ≤ K * (C₀ * kineticLinkScale d γ δ L) := by unfold kineticLinkScale; positivity
  let W : ℝ := C₂ * L ^ (-(incoherenceExponent d γ - η))
  have hW : 0 ≤ W := mul_nonneg (zero_le_one.trans hC₂) (Real.rpow_nonneg hLp.le _)
  have hbound (i : Fin n) : filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i) ≤
      ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) * if (Q i).IsIncoherent then W else 1) := by
    have h := hb L hL (Q i) (hspan i) K (φ i) (hφ i)
    by_cases hi : (Q i).IsIncoherent
    · rw [ite_eq_left hi]
      convert h.2 hi using 1
      congr 1
      dsimp only [W]
      ring
    · rw [ite_eq_right hi, mul_one]
      exact h.1
  calc
    _ ≤ ∏ i, ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) * if (Q i).IsIncoherent then W else 1) :=
      Finset.prod_le_prod fun i _ => hbound i
    _ = ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n * W ^ incoherenceCount Q) := by
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rw [prod_link_weights]
      · intro i _
        exact mul_nonneg hbase (by split_ifs <;> positivity)
    _ = _ := by
      dsimp only [W]
      rw [mul_pow C₂ (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← mul_assoc, ← Real.rpow_natCast (L ^ (-(incoherenceExponent d γ - η))) (incoherenceCount Q),
        ← Real.rpow_mul hLp.le]

/-! ### `AbsorbedProductDecay` -/

theorem exists_absorbed_filtLinkMassProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        (∏ i, filtLayerLinkMass L (δ * L ^ (2 * γ)) (Q i) (φ i)) ≤
          ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_filtLinkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨C₂, L₁, hC₂, hL₁, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₂, hL₂, ha⟩ := exists_counted_constant_absorption_threshold (zero_le_one.trans hC₂) hη
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan K hK φ hφ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLp := zero_lt_one.trans_le (hL₁.trans hLa)
  apply (hb L hLa n Q hspan K hK φ hφ).trans
  apply ENNReal.ofReal_le_ofReal
  have hbase : 0 ≤ (K * (C₀ * kineticLinkScale d γ δ L)) ^ n := by unfold kineticLinkScale; positivity
  calc
    _ ≤ (K * (C₀ * kineticLinkScale d γ δ L)) ^ n * L ^ (η * incoherenceCount Q) *
        L ^ (-(incoherenceExponent d γ - η) * incoherenceCount Q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha L hLb _) hbase) (Real.rpow_nonneg hLp.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hLp]
      congr 2
      ring

theorem exists_absolute_filtLinkProduct_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        (∫⁻ t in I, ‖∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖ₑ) ≤
          ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_filtLinkMassProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ I hI
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  exact (lintegral_linkProduct_enorm_leFilt hLp γ δ Q φ hI).trans (hb L hL n Q hspan K hK φ hφ)

end WaveTurbulence.Flower.FiltProd

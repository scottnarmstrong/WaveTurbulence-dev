/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Shift
/-! # D5a FILT-LINK: o82 Lemma 14.1, (14.1) — the filtered pair mass

`exists_filtOneLink_decay` is main's `Incoh.exists_oneLink_decay` (TARGET (incohproof16)) for the filtered link of a
`K`-presented multiplier: the same quantifier order and the same bound, times `K`. The base constant `C₀` depends
only on `d` (not on `δ`, the layers or the multiplier); the incoherent constant `C₂` is chosen after `δ` and the
layer span `D` (as in main, where it is absorbed into the incoherency power later). The proof is
`filtLayerLinkMass_le_of_shift` (the (14.2) mixture) applied to `exists_shift_linkMass_bounds`, followed by main's
scale algebra (`coherent_scale_identity`, `incoherent_scale_identity`, `incoherent_gain_le`), as in main's
`exists_factored_linkMass_bounds` and `exists_oneLink_decay`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

/-- The filtered one-link bounds in factored source exponents (main's `exists_factored_linkMass_bounds`, times `K`). -/
theorem exists_filt_factored_linkMass_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₁ L₀ : ℝ, 0 < C₁ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D →
        ∀ (K : ℝ) (φ : ℝ → ℂ), PresentedMult L K φ →
        (filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤
          ENNReal.ofReal K * ENNReal.ofReal (kineticLinkScale d γ δ L *
            (C₀ + C₁ * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)))) ∧
        (Q.IsIncoherent → filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤
          ENNReal.ofReal K * ENNReal.ofReal (kineticLinkScale d γ δ L *
            (C₀ * δ⁻¹ * L ^ (-2 * γ) + C₁ * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_shift_linkMass_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη δ hδ D hD
  obtain ⟨C₁, L₀, hC₁, hL₀, hb⟩ := hb γ hγ η hη δ hδ D hD
  refine ⟨C₁, L₀, hC₁, hL₀, ?_⟩
  intro L hL Q hspan K φ hP
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hraw := hb L hL Q hspan
  constructor
  · apply (filtLayerLinkMass_le_of_shift hLp _ Q hP _ fun c => (hraw c).1).trans_eq
    congr 2
    rw [← Real.rpow_natCast L (2 * d)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [coherent_scale_identity hLp]
    rw [show 2 * (d : ℝ) - 2 * γ = 2 * ((d : ℝ) - γ) by ring]
    rfl
  · intro hQ
    apply (filtLayerLinkMass_le_of_shift hLp _ Q hP _ fun c => (hraw c).2 hQ).trans_eq
    congr 2
    rw [← Real.rpow_natCast L (2 * d)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [incoherent_scale_identity hLp]
    rw [show 2 * (d : ℝ) - 2 * γ = 2 * ((d : ℝ) - γ) by ring]
    rfl

/-- **o82 Lemma 14.1, (14.1)** in main's normalization: the filtered link of a `K`-presented multiplier `φ` (o82's
`A_H`, filters at scales `≥ L`) has the pair mass of main's `exists_oneLink_decay`, times `K`: `C₀ L^{2d}/μ`, and
for unequal layers the additional `C₂ L^{-(incoherenceExponent − η)}`. -/
theorem exists_filtOneLink_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D →
        ∀ (K : ℝ) (φ : ℝ → ℂ), PresentedMult L K φ →
        (filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤
          ENNReal.ofReal (K * (C₀ * kineticLinkScale d γ δ L))) ∧
        (Q.IsIncoherent → filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤
          ENNReal.ofReal (K * (C₀ * C₂ * kineticLinkScale d γ δ L *
            L ^ (-(incoherenceExponent d γ - η))))) := by
  obtain ⟨C, hC, hb⟩ := exists_filt_factored_linkMass_bounds d hd
  refine ⟨C + 1, by positivity, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨B, L₁, hB, hL₁, hb⟩ := hb γ hγ η hη δ hδ D hD
  have hexp : 0 < 2 * ((d : ℝ) - 1) * (1 - γ) - η := by
    linarith [incoherenceExponent_le_longGain d γ]
  obtain ⟨L₂, hL₂, hsmall⟩ := exists_decaying_constant_threshold (C := B) hexp
  let C₂ : ℝ := max 1 (C * δ⁻¹ + B)
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hC₂₀ : 0 ≤ C₂ := zero_le_one.trans hC₂
  have hbig : C * δ⁻¹ + B ≤ (C + 1) * C₂ := by
    have hm : C * δ⁻¹ + B ≤ C₂ := le_max_right _ _
    nlinarith only [hm, mul_nonneg hC.le hC₂₀]
  refine ⟨C₂, max L₁ L₂, hC₂, (hL₁.trans (le_max_left _ _)), ?_⟩
  intro L hL Q hspan K φ hP
  have hLa : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLb : L₂ ≤ L := (le_max_right _ _).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hbase : 0 ≤ kineticLinkScale d γ δ L := by unfold kineticLinkScale; positivity
  have hdecay : B * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η) ≤ 1 := by
    have h := hsmall L hLb
    rw [show -(2 * ((d : ℝ) - 1) * (1 - γ) - η) =
      -(2 * ((d : ℝ) - 1) * (1 - γ)) + η by ring] at h
    exact h
  have hraw := hb L hLa Q hspan K φ hP
  constructor
  · apply hraw.1.trans
    calc
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((C + 1) * kineticLinkScale d γ δ L) := by
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        calc
          _ ≤ kineticLinkScale d γ δ L * (C + 1) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hdecay) hbase
          _ = _ := by ring
      _ = _ := (ENNReal.ofReal_mul' (by positivity)).symm
  · intro hQ
    apply (hraw.2 hQ).trans
    calc
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((C + 1) * C₂ * kineticLinkScale d γ δ L *
            L ^ (-(incoherenceExponent d γ - η))) := by
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        calc
          _ ≤ kineticLinkScale d γ δ L *
              ((C * δ⁻¹ + B) * L ^ (-(incoherenceExponent d γ - η))) :=
            mul_le_mul_of_nonneg_left (incoherent_gain_le hLone hη.le (by positivity) hB.le) hbase
          _ ≤ kineticLinkScale d γ δ L *
              (((C + 1) * C₂) * L ^ (-(incoherenceExponent d γ - η))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hLp.le _)) hbase
          _ = _ := by ring
      _ = _ := (ENNReal.ofReal_mul' (by positivity)).symm

end WaveTurbulence.Flower.FiltLink

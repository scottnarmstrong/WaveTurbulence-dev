/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Envelope
public import WaveTurbulence.Foundations.Incoh.RootDensityLp

/-! # D5b-2 FILT-PROD: selected-coordinate density bounds (twins of `SelectedDensityBound`, `RootDensityEndpoints`,
`RootDensityLp`). The decay constant `C₀` is `K`-free; the bounds read `(K * C₀ * δ)^n`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc

theorem exists_selectedDensityFilt_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ r : ℕ, ∀ R : RootCoordinates n r, ∀ t : Fin r → ℝ,
        ‖RootCoordinates.linkDensityFilt R L γ δ Q φ I t‖ₑ ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) *
            L ^ ((d : ℝ) * r)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_replacedFiltLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ I hbox r R t
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hB : ∀ i u, ‖φ i u‖ ≤ K := fun i u => PresentedMult.norm_le (hφ i) hLp.le hK u
  have hKC : 0 ≤ K * C₀ := mul_nonneg hK hC₀.le
  apply (RootCoordinates.enorm_linkDensity_le_envelopeFilt R K hLone hδ γ Q φ hK hB hbox t).trans
  calc
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        (∏ i, replacedLinkMassFilt K L γ δ Q φ R.rootLinks i) :=
      mul_le_mul' le_rfl (RootCoordinates.lintegral_envelope_le_replacedMassFilt R K hLone γ δ Q φ hK)
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * r)) :=
      mul_le_mul' le_rfl (hb L hL n Q hspan K hK φ hφ r R.rootLinks R.card_rootLinks_le)
    _ = ENNReal.ofReal (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (K * C₀ * kineticLinkScale d γ δ L) ^ n) *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * r)) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      rw [mul_assoc K C₀]
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hKC γ) (Real.rpow_nonneg hLp.le _))
        (Real.rpow_nonneg hLp.le _)

theorem exists_rootDensityFilt_endpoint_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        (eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) 1 ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))) ∧
        (∀ t, ‖RootCoordinates.linkDensityFilt R L γ δ Q φ I t‖ₑ ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) *
            ENNReal.ofReal (L ^ (2 * (d : ℝ)))) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_rootDensityFilt_L1_bound d hd
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_selectedDensityFilt_bound d hd
  let C₀ := C₁ + C₂
  have hC₀ : 0 < C₀ := add_pos hC₁ hC₂
  have hC₁₀ : C₁ ≤ C₀ := by dsimp [C₀]; linarith
  have hC₂₀ : C₂ ≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb₁⟩ := hb₁ γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₂, hL₂, hb₂⟩ := hb₂ γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan K hK φ hφ I hI hbox R
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLp := zero_lt_one.trans_le (hL₁.trans hLa)
  have hpow₁ : (K * C₁ * δ) ^ n ≤ (K * C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hK hC₁.le) hδ.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC₁₀ hK) hδ.le) n
  have hpow₂ : (K * C₂ * δ) ^ n ≤ (K * C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hK hC₂.le) hδ.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC₂₀ hK) hδ.le) n
  have hA : 0 ≤ (K * C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) := by
    positivity
  constructor
  · exact (hb₁ L hLa n Q hspan K hK φ (fun i => (hφ i)) I hI hbox R).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hpow₁ (Real.rpow_nonneg hLp.le _)))
  · intro t
    rw [← ENNReal.ofReal_mul hA]
    have hpoint := hb₂ L hLb n Q hspan K hK φ hφ I hbox 2 R t
    norm_num only [Nat.cast_ofNat] at hpoint
    rw [mul_comm (d : ℝ) 2] at hpoint
    exact hpoint.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow₂ (Real.rpow_nonneg hLp.le _)) (Real.rpow_nonneg hLp.le _)))

theorem exists_rootDensityFilt_Lp_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) (ENNReal.ofReal (1 + 3 * η)) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensityFilt_endpoint_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan K hK φ hφ I hI hbox R
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hF := (RootCoordinates.integrable_linkDensityFilt R hLp γ δ Q φ hI hbox).aestronglyMeasurable
  have hend := hb L hL n Q hspan K hK φ hφ I hI hbox R
  have hp : 1 ≤ 1 + 3 * η := by linarith
  have hp₀ : 0 < 1 + 3 * η := by positivity
  have hβ : 0 ≤ 1 - 1 / (1 + 3 * η) := sub_nonneg.mpr ((div_le_one hp₀).mpr hp)
  have hA : 0 ≤ (K * C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) := by
    positivity
  have hdim : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hg' : (1 : ℝ) ≤ incoherenceCount Q := by exact_mod_cast hg
  have hbudget := couple_interpolation_loss_budget hdim hη.le hg'
  apply (eLpNorm_le_of_one_and_scaled_pointwise hF hp hend.1
    (Filter.Eventually.of_forall hend.2)).trans
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hLp.le (2 * (d : ℝ))) hβ,
    ← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_mul hLp.le, mul_assoc, ← Real.rpow_add hLp]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hLone ?_) (by positivity)
  nlinarith only [hbudget]

end WaveTurbulence.Flower.FiltProd

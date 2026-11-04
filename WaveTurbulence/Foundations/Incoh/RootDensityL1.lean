/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootCoordinates
public import WaveTurbulence.Foundations.Incoh.NormalizedIntegrand

/-!
# L¹ decay of the actual root density

TARGET (incohproof17)–(incohproof18). Integrate the literal normalized
localized integrand over the non-root times. The product estimate gives
the root L¹ norm; no endpoint norm is stored in the carrier.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The source root density, formed as the actual normalized time marginal. -/
@[expose] def RootCoordinates.linkDensity {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    (Fin r → ℝ) → ℂ :=
  R.density (normalizedLinkIntegrand L γ δ Q I)

/-- Actual root densities are integrable for every measurable source time domain. -/
theorem RootCoordinates.integrable_linkDensity {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (R.linkDensity L γ δ Q I) :=
  R.integrable_density (integrable_normalizedLinkIntegrand hL γ δ Q hI hbox)

/-- TARGET (incohproof18), the actual root-density L¹ bound uniformly over structural root choices. -/
theorem exists_rootDensity_L1_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        eLpNorm (R.linkDensity L γ δ Q I) 1 ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedLinkIntegrand_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hI hbox R
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hF := integrable_normalizedLinkIntegrand hLp γ δ Q hI hbox
  rw [eLpNorm_one_eq_lintegral_enorm (R.integrable_linkDensity hLp γ δ Q hI hbox).aestronglyMeasurable]
  exact (R.lintegral_density_le hF).trans (hb L hL n Q hspan I hI hbox)

end WaveTurbulence.Incoh

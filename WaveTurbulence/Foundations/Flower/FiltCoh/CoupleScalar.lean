/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolEnvelope
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalUniform
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarProfile
public import WaveTurbulence.Foundations.Spine.RA1LW.ErrorCommonConstant
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceCoefficientWeights
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ScalarEnvelopeSum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ExpansionCardinality
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalRemainderJoint

/-! # FILT-COH: the whole physical scalar of a layer-zero couple at an arbitrary time weight

`physicalScalar` is the integrand of main's exact global identity
`RA1Leafwise.couple_physical_global_profiles_uniform` (all coefficient sets `Z` together). Its envelope at weight
`θ ≤ 1 - η/8` has a geometric mass, with no `L` loss and no principal value. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- The literal global physical scalar of a couple: main's identity integrand, summed over the coefficient sets. -/
@[expose] def physicalScalar (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) (β γ' : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  ζ * ∑ Z : (chosenSet Q.links).powerset,
    (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹) *
      physicalWeightedCellSymbol L δ γ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam

/-- Joint measurability of the physical cell symbol in `λ` and both modulation arrays. -/
theorem stronglyMeasurable_physicalWeightedCellSymbol_joint {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      physicalWeightedCellSymbol L δ γ z p.2.1 p.2.2 J C p.1) := by
  have hs : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z p.2.1 p.2.2)
        (resProfile J (fun Ω => C (ofLp Ω) p.1))) := by
    apply measurable_approxSum_parameter L (L^(2*γ)*(2*δ)) J
      (W := fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) => halfCellAmplitude z p.2.1 p.2.2)
      (C := fun α p => C α p.1)
    · intro x y
      have hb := (continuous_halfCellAmplitude_joint z).measurable
      have hm : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          (p.2,(x,y))) := measurable_snd.prodMk measurable_const
      have hh := hb.comp hm
      exact hh
    · intro α
      have hb : StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          C α p.1) := hC.comp_measurable (measurable_const.prodMk measurable_fst)
      exact hb.measurable
  have hw := stronglyMeasurable_normalizedWickCorrection_joint (d := d) hL (2*δ) γ z J hC
  have he : (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      physicalWeightedCellSymbol L δ γ z p.2.1 p.2.2 J C p.1) =
      fun p => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z p.2.1 p.2.2)
          (resProfile J (fun Ω => C (ofLp Ω) p.1)) +
        ((4:ℂ)^n)⁻¹ * normalizedWickCorrection L (2*δ) γ z p.2.1 p.2.2 J C p.1 := by
    funext p
    exact physicalWeightedCellSymbol_eq_sum_add_wick hL δ γ z p.2.1 p.2.2 J C p.1
  rw [he]
  exact (hs.stronglyMeasurable.const_mul _).add (hw.const_mul _)

/-- Joint measurability of the whole physical scalar. -/
theorem stronglyMeasurable_physicalScalar_joint (Q : RegCpl) {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ Z, StronglyMeasurable (Function.uncurry (C Z)))
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
        physicalScalar L δ γ Q ζ C p.1 p.2.1 p.2.2 z) := by
  classical
  unfold physicalScalar
  apply StronglyMeasurable.const_mul
  apply Finset.stronglyMeasurable_fun_sum
  intro Z _
  exact (stronglyMeasurable_physicalWeightedCellSymbol_joint hL δ γ _ (hC Z) z).const_mul _

end WaveTurbulence.Flower.FiltCoh

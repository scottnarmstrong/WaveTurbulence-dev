/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialHigherEnvelope
public import WaveTurbulence.Foundations.RegAsymp.SeparatedEnvelope

/-! # Separated mass of the measurable scalar derivative envelope -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp ClassJR
open scoped ENNReal

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
  {d : ℕ} (N W : ℕ)
  (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
    (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ) (F : Mom d → ℂ)
  (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- The finite link cover and individual higher leaf moments dominate the
literal real derivative envelope, before source-frequency integration. -/
theorem ofReal_leafScalarDerivativeEnvelope_le
    (lam : ℝ × ℝ) {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hb : ∀ z β γ', ‖R lam β γ' z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r)*B)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    ENNReal.ofReal (leafScalarDerivativeEnvelope hQ hG N W R F S (lam,p)) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*r*spectralFrequencyLoss Q)) * ENNReal.ofReal B *
        leafSpatialHigherEnvelope (N+1) W F S p := by
  classical
  by_cases hm : p.1.2 ∈ S p.1.1
  · have hh := ENNReal.ofReal_le_ofReal
      (leafScalarDerivativeEnvelope_le hQ hG N W R F S (lam,p) hr hB hb)
    apply hh.trans_eq
    simp only [leafSpatialHigherEnvelope,hm,ite_true,leafHigherMomentWeight]
    have hcenter : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (p.1.1 a))^W :=
      Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
    have hD : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) N W := by
      unfold maskedSourceSpatialConstant
      have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
      positivity
    have hK : 0 ≤ (1+2*Real.pi)*r*spectralFrequencyLoss Q := by
      unfold spectralFrequencyLoss; positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),ofReal_norm]
    ac_rfl
  · simp only [leafScalarDerivativeEnvelope,leafScalarAmplitude,hm,ite_false,
      norm_zero,mul_zero,ENNReal.ofReal_zero,zero_le]

/-- Conditional transport of the local NT scalar envelope into its actual
full spatial sample mass. The source application constructs B from J3. -/
theorem weighted_mass_leafScalarDerivativeEnvelope_le
    {K M : ℕ}
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R p.1 p.2.1 p.2.2 z)) {Binput : ℝ} (hK : d+1 ≤ K) (hBi : 0 ≤ Binput)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput)
    (η : ℝ) {r : ℝ} (hr : 0 ≤ r) (B : (ℝ × ℝ) → ℝ)
    (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ',
      ‖R lam β γ' z‖ ≤
        ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r)*B lam) :
    (∫⁻ q, wL η q.1 * ENNReal.ofReal
      (leafScalarDerivativeEnvelope hQ hG N W R F S q)
      ∂volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*r*spectralFrequencyLoss Q)) *
        (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
        (∫⁻ p, leafSpatialHigherEnvelope (N+1) W F S p
          ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  apply weighted_lintegral_le_separated _ η _
    (measurable_leafScalarDerivativeEnvelope hQ hG N W R F S hR hK hBi hF)
    _ (measurable_leafSpatialHigherEnvelope (N+1) W hK hBi hF S) B hB
  filter_upwards [hb] with lam hlam
  intro p
  exact ofReal_leafScalarDerivativeEnvelope_le hQ hG N W R F S lam hr (hBn lam) hlam p

end WaveTurbulence.RegAsymp

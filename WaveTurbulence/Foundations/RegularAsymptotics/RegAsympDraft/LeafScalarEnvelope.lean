/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarAmplitude
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafModulationMoment
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialHigherEnvelope
public import WaveTurbulence.Foundations.RegAsymp.MaskedModulationMeasurable
public import WaveTurbulence.Foundations.RegAsymp.RootFrequencyMoment

/-! # Actual derivative envelopes for measurable leaf scalar amplitudes -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp
open scoped ContDiff ENNReal

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
  {d : ℕ} (N W : ℕ)
  (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
    (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
  (F : Mom d → ℂ)
  (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- A pointwise envelope retaining the actual scalar, including exceptional frequencies. -/
def leafScalarDerivativeEnvelope
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) : ℝ :=
  maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
    (∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W) *
    (1+‖∑ a, toLp 2 (q.2.2 a)‖)^N * ‖leafScalarAmplitude hQ hG R F S q‖

theorem leafScalarDerivativeEnvelope_nonneg
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    0 ≤ leafScalarDerivativeEnvelope hQ hG N W R F S q := by
  have hcenter : 0 ≤ ∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W :=
    Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
  unfold leafScalarDerivativeEnvelope maskedSourceSpatialConstant
  positivity

theorem weighted_derivative_maskedLeafScalarDensity_le {j : ℕ} (hj : j ≤ N)
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    Fourier.momentumBracket k^W * ‖iteratedFDeriv ℝ j (maskedLeafScalarDensity hQ hG R F S q) k‖ ≤
      leafScalarDerivativeEnvelope hQ hG N W R F S q :=
  weighted_norm_iteratedFDeriv_maskedModulation_le q.2.1.1
    (leafScalarAmplitude hQ hG R F S q) (∑ a, toLp 2 (q.2.2 a)) k hj

theorem measurable_leafScalarDerivativeEnvelope {K M : ℕ}
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R p.1 p.2.1 p.2.2 z))
    {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B) :
    Measurable (leafScalarDerivativeEnvelope hQ hG N W R F S) := by
  have hv : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      LeafSpatialSample d Q.links.length (2*Q.links.length+1) => ∑ a, toLp 2 (q.2.2 a)) := by
    have hc : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact hc.stronglyMeasurable.comp_measurable measurable_snd.snd
  have ha : StronglyMeasurable (leafScalarAmplitude hQ hG R F S) :=
    stronglyMeasurable_leafScalarAmplitude hQ hG R hR hK hB hF S
  have hc : Measurable (fun q : (ℝ × ℝ) ×
      LeafSpatialSample d Q.links.length (2*Q.links.length+1) => q.2.1.1) := measurable_snd.fst.fst
  exact measurable_maskedModulation_envelope N W _ hc _ ha _ hv

/-- The scalar estimate costs only one frequency moment per leaf. -/
theorem leafScalarDerivativeEnvelope_le
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1))
    {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hb : ∀ z β γ', ‖R q.1 β γ' z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r)*B) :
    leafScalarDerivativeEnvelope hQ hG N W R F S q ≤
      maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*r*spectralFrequencyLoss Q) *
        (∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W) *
        (∏ a, (1+‖toLp 2 (q.2.2 a)‖)^(N+1))*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B := by
  classical
  let D := maskedSourceSpatialConstant d (2*Q.links.length+1) N W
  let P := ∏ a, Fourier.momentumBracket (NTSP.intVec (q.2.1.1 a))^W
  let K := (1+2*Real.pi)*r*spectralFrequencyLoss Q
  have hD : 0 ≤ D := by
    dsimp only [D,maskedSourceSpatialConstant]
    have hmask := zero_le_one.trans (one_le_rootMaskDerivativeConstant d N)
    positivity
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ =>
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hK : 0 ≤ K := by dsimp only [K,spectralFrequencyLoss]; positivity
  have hn : ‖leafScalarAmplitude hQ hG R F S q‖ ≤
      K*((1+∑ a, ‖toLp 2 (q.2.2 a)‖)*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖)*B := by
    by_cases hm : q.2.1.2 ∈ S q.2.1.1
    · simp only [leafScalarAmplitude,hm,ite_true,norm_mul]
      have hh := mul_le_mul_of_nonneg_left
        (hb q.2.1.2 (leafModulations hQ hG q.2.2).1 (leafModulations hQ hG q.2.2).2)
        (norm_nonneg (leafSpectrumCoefficient F q.2.1.1 q.2.2))
      apply hh.trans
      have hw : 1+((∑ i, ‖(leafModulations hQ hG q.2.2).1 i‖)+
          (∑ i, ‖(leafModulations hQ hG q.2.2).2 i‖)) ≤
          spectralFrequencyLoss Q*(1+∑ a, ‖toLp 2 (q.2.2 a)‖) :=
        leaf_modulation_weight_le hQ hG q.2.2
      have hs : 0 ≤ (1+2*Real.pi)*r*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B := by positivity
      have hm' := mul_le_mul_of_nonneg_left hw hs
      simpa only [K,mul_assoc,mul_left_comm,mul_comm] using hm'
    · simp only [leafScalarAmplitude,hm,ite_false,norm_zero]
      positivity
  unfold leafScalarDerivativeEnvelope
  calc
    _ ≤ D*P*(1+‖∑ a, toLp 2 (q.2.2 a)‖)^N *
        (K*((1+∑ a, ‖toLp 2 (q.2.2 a)‖)*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖)*B) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (D*K*P*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B)*
        ((1+‖∑ a, toLp 2 (q.2.2 a)‖)^N*(1+∑ a, ‖toLp 2 (q.2.2 a)‖)) := by ring
    _ ≤ (D*K*P*‖leafSpectrumCoefficient F q.2.1.1 q.2.2‖*B)*
        (∏ a, (1+‖toLp 2 (q.2.2 a)‖)^(N+1)) :=
      mul_le_mul_of_nonneg_left (root_frequency_moment_mul_le_product (fun a => toLp 2 (q.2.2 a)) N)
        (by positivity)
    _ = _ := by ring

end WaveTurbulence.RegAsymp

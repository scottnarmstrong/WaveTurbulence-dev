/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarMass
public import WaveTurbulence.Foundations.Incoh.SpatialNormParameterIntegral

/-! # Spatial norm of the original masked leaf mixture of a measurable scalar -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp
open scoped ENNReal ContDiff

/-- Conditional spatial transport for the actual masked amplitude. In the
leading-term application the scalar is the actual half-cell singInt,
whose geometric linear-frequency bound is already proved. -/
theorem leafScalar_spatialNorm_and_integrable_of_envelope {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d N W K M : ℕ}
    (R : (Fin Q.links.length → Mom d) → (Fin Q.links.length → Mom d) →
      ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p :
      (Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d) => R p.1 p.2 z))
    {F : Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2+N ≤ K) (hM : W+2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ z β γ', ‖R β γ' z‖ ≤ (1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r) :
    (∀ k : Mom d, Integrable (fun p =>
      maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p) k)
        (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ∧
    Fourier.spatialNorm N W (fun k => ∫ p,
      maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p) k
        ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) ≤
      ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
        ((1+2*Real.pi)*r*spectralFrequencyLoss Q)) *
        (ENNReal.ofReal (Ccover^Q.links.length)*
          ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1)) := by
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let v := fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
    leafScalarDerivativeEnvelope hQ hG N W (fun _ => R) F S ((0,0),p)
  let D := maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
    ((1+2*Real.pi)*r*spectralFrequencyLoss Q)
  have hR' (z) : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R q.2.1 q.2.2 z) :=
    (hR z).comp_measurable measurable_snd
  have hmap : Measurable (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      (((0,0):ℝ × ℝ),p)) := measurable_const.prodMk measurable_id
  have hm : Measurable v :=
    (measurable_leafScalarDerivativeEnvelope hQ hG N W (fun _ => R) F S hR' (by omega) hBi hF).comp hmap
  have hvn (p) : 0 ≤ v p := leafScalarDerivativeEnvelope_nonneg hQ hG N W (fun _ => R) F S ((0,0),p)
  have hbound (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
      ENNReal.ofReal (v p) ≤ ENNReal.ofReal D * leafSpatialHigherEnvelope (N+1) W F S p := by
    have hh := ofReal_leafScalarDerivativeEnvelope_le hQ hG N W (fun _ => R) F S
      (0,0) hr (by norm_num : (0:ℝ) ≤ 1) (fun z β γ' => by simpa only [mul_one] using hb z β γ') p
    simpa only [ENNReal.ofReal_one,mul_one] using hh
  have hleaf := lintegral_leafSpatialHigherEnvelope_le (N+1) W (by omega) hM hBi hF S hcard
  have hmass : (∫⁻ p, ENNReal.ofReal (v p) ∂μ) ≤
      ENNReal.ofReal D * ∫⁻ p, leafSpatialHigherEnvelope (N+1) W F S p ∂μ := by
    apply (lintegral_mono hbound).trans_eq
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hv : Integrable v μ := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (∫⁻ p, ‖v p‖ₑ ∂μ) = ∫⁻ p, ENNReal.ofReal (v p) ∂μ :=
      lintegral_congr (fun p => Real.enorm_eq_ofReal (hvn p))
    rw [he]
    exact hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hleaf.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness))))
  have ha : StronglyMeasurable (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      leafScalarAmplitude hQ hG (fun _ => R) F S ((0,0),p)) :=
    (stronglyMeasurable_leafScalarAmplitude hQ hG (fun _ => R) hR' (by omega) hBi hF S).comp_measurable hmap
  have hc : Measurable (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) => p.1.1) := measurable_fst.fst
  have hfreq : StronglyMeasurable (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      ∑ a, toLp 2 (p.2 a)) := by
    have ht : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact ht.stronglyMeasurable.comp_measurable measurable_snd
  have hderiv (k : Mom d) (j : ℕ) : StronglyMeasurable
      (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
        iteratedFDeriv ℝ j (maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p)) k) :=
    stronglyMeasurable_derivative_maskedModulation _ hc _ ha _ hfreq k j
  have hiA (k : Mom d) : Integrable (fun p =>
      maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p) k) μ := by
    have hmask : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
      measurable_of_countable _
    have hchar : Continuous (fun v : Mom d => (Real.fourierChar (inner ℝ v k):ℂ)) := by fun_prop
    have hsm : StronglyMeasurable (fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
        maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p) k) :=
      (hmask.stronglyMeasurable.comp_measurable hc).mul
        (ha.mul (hchar.stronglyMeasurable.comp_measurable hfreq.measurable))
    apply hv.mono' hsm.aestronglyMeasurable
    apply ae_of_all
    intro p
    have hh := weighted_derivative_maskedLeafScalarDensity_le hQ hG N W (fun _ => R) F S
      (j := 0) (Nat.zero_le N) ((0,0),p) k
    exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_momentumBracket k))).trans
      (by simpa only [norm_iteratedFDeriv_zero] using hh)
  refine ⟨hiA,?_⟩
  have hh := spatialNorm_integral_le_of_uniform_derivative_envelope μ
    (fun k p => maskedLeafScalarDensity hQ hG (fun _ => R) F S ((0,0),p) k) v
    (fun p => (contDiff_maskedModulation p.1.1 _ _).of_le (by simp))
    (fun j _hj k => (hderiv k j).aestronglyMeasurable) hv
    (fun j hj k p => weighted_derivative_maskedLeafScalarDensity_le hQ hG N W (fun _ => R) F S hj ((0,0),p) k)
  apply hh.trans
  have he : ENNReal.ofReal (∫ p, v p ∂μ) = ∫⁻ p, ENNReal.ofReal (v p) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hv (ae_of_all _ hvn)
  rw [he]
  exact hmass.trans (mul_le_mul' le_rfl hleaf)

end WaveTurbulence.RegAsymp

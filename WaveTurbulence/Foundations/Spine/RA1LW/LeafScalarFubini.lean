/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarMass
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileFubini
public import WaveTurbulence.Foundations.RegAsymp.PairedSpatialMixture

/-! # Original masked source envelopes give actual joint L1 and global profile Fubini -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp ClassJR WaveTurbulence.Fourier
open scoped ENNReal

/-- Conditional analytic transport from an original measurable scalar
source envelope to actual joint integrability and sample/time Fubini.
The source NT and Wick applications derive these envelopes from SRep. -/
theorem leafScalar_joint_integrable_and_profile_swap_of_envelope {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R p.1 p.2.1 p.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : (∀ a, spatialNorm K M (F a) ≤ ENNReal.ofReal Binput))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {η : ℝ} (hη : 0 ≤ η) {r : ℝ} (hr : 0 ≤ r) {B : ℝ × ℝ → ℝ}
    (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hBfin : (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ', ‖R lam β γ' z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r)*B lam) :
    (∀ k : Mom d, Integrable (fun q => maskedLeafScalarDensity hQ hG R F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) ∧
    ∀ (k : Mom d) (t : Fin 2 → ℝ),
      pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hG R F S (lam,p) k
        ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t =
      ∫ p, pairedInverseProfile (fun lam => maskedLeafScalarDensity hQ hG R F S (lam,p) k) t
        ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1) := by
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  let v := leafScalarDerivativeEnvelope hQ hG 0 0 R F S
  have hvm : Measurable v :=
    measurable_leafScalarDerivativeEnvelope hQ hG 0 0 R F S hR (by omega) hBi hF
  have hvn : ∀ q, 0 ≤ v q := leafScalarDerivativeEnvelope_nonneg hQ hG 0 0 R F S
  have hmass := weighted_mass_leafScalarDerivativeEnvelope_le hQ hG 0 0 R F S
    hR (by omega) hBi hF η hr B hB hBn hb
  have hleaf := lintegral_leafSpatialHigherEnvelope_le (0+1) 0 (by omega) (by omega) hBi hF S hcard
  have hfin : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) < ⊤ :=
    hmass.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin)
      (hleaf.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness))))
  have hv : Integrable v (volume.prod μ) := integrable_of_weighted_lintegral_lt_top μ hη v hvm hvn hfin
  have ha : StronglyMeasurable (leafScalarAmplitude hQ hG R F S) :=
    stronglyMeasurable_leafScalarAmplitude hQ hG R hR (by omega) hBi hF S
  have hc : Measurable (fun q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      q.2.1.1) := measurable_snd.fst.fst
  have hvfreq : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      LeafSpatialSample d Q.links.length (2*Q.links.length+1) => ∑ a, toLp 2 (q.2.2 a)) := by
    have hc' : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact hc'.stronglyMeasurable.comp_measurable measurable_snd.snd
  have hsm (k : Mom d) : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      maskedLeafScalarDensity hQ hG R F S q k) := by
    have hmask : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
      measurable_of_countable _
    have hchar : Continuous (fun v : Mom d => (Real.fourierChar (inner ℝ v k):ℂ)) := by fun_prop
    exact (hmask.stronglyMeasurable.comp_measurable hc).mul
      (ha.mul (hchar.stronglyMeasurable.comp_measurable hvfreq.measurable))
  have hi (k : Mom d) : Integrable (fun q => maskedLeafScalarDensity hQ hG R F S q k)
      (volume.prod μ) := by
    apply hv.mono' (hsm k).aestronglyMeasurable
    apply ae_of_all
    intro q
    have hh := weighted_derivative_maskedLeafScalarDensity_le hQ hG 0 0 R F S (j := 0)
      (by omega) q k
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hh
  exact ⟨hi,fun k t => pairedInverseProfile_integral_swap μ (hi k) t⟩

end WaveTurbulence.RA1Leafwise

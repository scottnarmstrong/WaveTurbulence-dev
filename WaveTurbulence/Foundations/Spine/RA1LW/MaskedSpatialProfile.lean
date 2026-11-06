/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.MaskedSpatialMass
public import WaveTurbulence.Foundations.RegAsymp.PairedSpatialMixture

/-! # Full spatial norm of the actual masked spectral remainder -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp ClassJR WaveTurbulence.Fourier
open scoped ENNReal ContDiff

/-- Conditional transport of the scalar local NT estimate into the landed
spatial restriction norm. All spatial derivatives act on the actual amplitude. -/
theorem maskedSpatial_profile_of_local_envelope {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d N W K M : ℕ}
    (hd : 3 ≤ d) (hn : 0 < Q.links.length) (L δ γ : ℝ)
    (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2+N ≤ K) (hM : W+2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : (∀ a, spatialNorm K M (F a) ≤ ENNReal.ofReal Binput))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {η : ℝ} (hη : 0 ≤ η) {T : Set (Fin 2 → ℝ)}
    (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1)
    {R : ℝ} (hR : 0 ≤ R) {B : (ℝ × ℝ) → ℝ}
    (hB : Measurable B) (hBn : ∀ lam, 0 ≤ B lam)
    (hBfin : (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ',
      ‖localRemainder (d := d) L δ γ J C β γ' lam z‖ ≤
        ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*R)*B lam) :
    mixedRestrictionNorm η N W T Set.univ
      (fun t k => pairedInverseProfile (fun lam => ∫ p,
        maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p k.val
          ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t.val) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) N W *
          ((1+2*Real.pi)*R*spectralFrequencyLoss Q)) *
          (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (N+1) M W*Binput)^(2*Q.links.length+1))) := by
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let := sFinite_leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let v := maskedSpatialDerivativeEnvelope hQ hG N W L δ γ J C F S
  have hvm : Measurable v :=
    measurable_maskedSpatialDerivativeEnvelope hQ hG hd hn N W L δ γ J hC (by omega) hBi hF S
  have hvn : ∀ q, 0 ≤ v q := maskedSpatialDerivativeEnvelope_nonneg hQ hG N W L δ γ J C F S
  have hmass := weighted_mass_maskedSpatialDerivativeEnvelope_le hQ hG N W L δ γ J C F S
    hd hn hC (by omega) hBi hF η hR B hB hBn hb
  have hleaf := lintegral_leafSpatialHigherEnvelope_le (N+1) W (by omega) hM hBi hF S hcard
  have hfin : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) < ⊤ :=
    hmass.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin)
      (hleaf.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness))))
  have hv : Integrable v (volume.prod μ) := integrable_of_weighted_lintegral_lt_top μ hη v hvm hvn hfin
  have hh := mixedRestrictionNorm_paired_spatialMixture_le μ hη
    (fun k q => maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2 k) v
    (fun q => (contDiff_maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S q.1 q.2).of_le (by simp))
    (fun k => stronglyMeasurable_maskedLeafSpatialRemainderDensity hQ hG hd hn L δ γ J hC (by omega) hBi hF S k)
    (fun j _hj k => (stronglyMeasurable_derivative_maskedLeafSpatialRemainderDensity hQ hG hd hn
      L δ γ J hC (by omega) hBi hF S k j).aestronglyMeasurable)
    hv hvm hvn
    (fun j hj k q => weighted_derivative_maskedLeafSpatialRemainderDensity_le hQ hG hj L δ γ J C F S q k) hT
  exact hh.trans (mul_le_mul' le_rfl (hmass.trans (mul_le_mul' le_rfl hleaf)))

end WaveTurbulence.RA1Leafwise

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceScalarProfile
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalDensityDecomposition

/-! # Exact global physical profile split with justified source integrals -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ApproxNT WithLp

/-- Analytic three-term assembly for the actual physical symbols.
Integrability of these explicit densities is derived from source SRep by
SourceRemainderFubini and SourceLeadingFubini. -/
theorem physical_source_profile_split_of_joint_integrable {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (hiN : Integrable (fun q => maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => localRemainder L (2*δ) γ J C β γ' lam z) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (hiA : Integrable (fun q => maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (hiW : Integrable (fun q => maskedLeafScalarDensity hQ hG
      (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' J C lam) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) (t : Fin 2 → ℝ) :
    sourceScalarProfile hQ hG
      (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' J C lam) F S t k =
    ((4:ℂ)^Q.links.length)⁻¹*sourceScalarProfile hQ hG
      (fun lam β γ' z => localRemainder L (2*δ) γ J C β γ' lam z) F S t k +
    sourceScalarProfile hQ hG
      (fun lam β γ' z => (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) F S t k +
    ((4:ℂ)^Q.links.length)⁻¹*sourceScalarProfile hQ hG
      (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' J C lam) F S t k := by
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  unfold sourceScalarProfile
  simp_rw [physical_masked_density_decomposition hQ hG hL]
  have h1 := pairedInverseProfile_integral_add μ
      ((hiN.const_mul (((4:ℂ)^Q.links.length)⁻¹)).add hiA)
      (hiW.const_mul (((4:ℂ)^Q.links.length)⁻¹)) t
  have h2 := pairedInverseProfile_integral_add μ
      (hiN.const_mul (((4:ℂ)^Q.links.length)⁻¹)) hiA t
  dsimp only [Pi.add_apply] at h1 h2
  rw [h1,h2]
  simp only [integral_const_mul,pairedInverseProfile_const_mul]
  rfl

end WaveTurbulence.RA1Leafwise

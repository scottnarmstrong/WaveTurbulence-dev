/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceLeadingApp
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalProfileSplit
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceCoefficientWeights

/-! # The literal combined scalar source error and its profile -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ApproxNT WithLp

/-- The original squared-Wick and NT errors, with original finite source
weights, original garden sign and exact physical2delta normalization. -/
def physicalErrorScalar {d : ℕ} (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) (β γ' : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  ζ * ∑ Z : (chosenSet Q.links).powerset,
    ((∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)*((4:ℂ)^Q.links.length)⁻¹)*
      (localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z +
        normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam)

/-- Conditional analytic assembly of the combined literal scalar error.
The source applications derive both joint-integrability premises from SRep. -/
theorem physicalErrorScalar_profile_of_joint_integrable {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (L δ γ : ℝ) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (hi : ∀ Z : (chosenSet Q.links).powerset,
      Integrable (fun q => maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ∧
      Integrable (fun q => maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) (t : Fin 2 → ℝ) :
    sourceScalarProfile hQ hG (physicalErrorScalar L δ γ Q ζ C) F S t k =
      ζ*∑ Z : (chosenSet Q.links).powerset,
        (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)*((4:ℂ)^Q.links.length)⁻¹*
          (sourceScalarProfile hQ hG
            (fun lam β γ' z => localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z) F S t k +
          sourceScalarProfile hQ hG
            (fun lam β γ' z => normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam) F S t k) := by
  classical
  let R : (chosenSet Q.links).powerset → (ℝ × ℝ) →
      (Fin Q.links.length → Mom d) → (Fin Q.links.length → Mom d) →
      ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ := fun Z lam β γ' z =>
    ((∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)*((4:ℂ)^Q.links.length)⁻¹)*
      (localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z +
        normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam)
  have hiR (Z : (chosenSet Q.links).powerset) :
      Integrable (fun q => maskedLeafScalarDensity hQ hG (R Z) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
    have hh := ((hi Z).1.add (hi Z).2).const_mul
      ((∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)*((4:ℂ)^Q.links.length)⁻¹)
    apply hh.congr
    apply ae_of_all
    intro q
    rcases q with ⟨lam,p⟩
    simp only [R,maskedLeafScalarDensity_const_mul,maskedLeafScalarDensity_add,Pi.add_apply]
  change sourceScalarProfile hQ hG (fun lam β γ' z => ζ*∑ Z, R Z lam β γ' z) F S t k = _
  rw [sourceScalarProfile_const_mul,sourceScalarProfile_finsetSum hQ hG F S Finset.univ R k (fun Z _ => hiR Z)]
  congr 1
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only [R]
  rw [sourceScalarProfile_const_mul,sourceScalarProfile_add hQ hG _ _ F S k (hi Z).1 (hi Z).2 t]

end WaveTurbulence.RA1Leafwise

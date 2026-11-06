/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.JointProfileLinearity
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceDensityIdentities

/-! # Literal sample-integrated scalar source inverse profiles -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh

/-- The actual masked source density is integrated over original spatial
samples, then inverted in the two temporal frequencies. -/
def sourceScalarProfile {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hG R F S (lam,p) k
    ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
variable (R R' : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
  (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
variable (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
variable (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
  Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- Source scalar multiplication retains both original integrals. -/
theorem sourceScalarProfile_const_mul (c : ℂ) (t : Fin 2 → ℝ) (k : Mom d) :
    sourceScalarProfile hQ hG (fun lam β γ z => c*R lam β γ z) F S t k =
      c*sourceScalarProfile hQ hG R F S t k := by
  unfold sourceScalarProfile
  simp only [maskedLeafScalarDensity_const_mul,integral_const_mul,pairedInverseProfile_const_mul]

/-- Source addition is lawful from actual joint integrability of its two densities. -/
theorem sourceScalarProfile_add (k : Mom d)
    (hiR : Integrable (fun q => maskedLeafScalarDensity hQ hG R F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (hiR' : Integrable (fun q => maskedLeafScalarDensity hQ hG R' F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) (t : Fin 2 → ℝ) :
    sourceScalarProfile hQ hG (fun lam β γ z => R lam β γ z+R' lam β γ z) F S t k =
      sourceScalarProfile hQ hG R F S t k+sourceScalarProfile hQ hG R' F S t k := by
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  unfold sourceScalarProfile
  simp only [maskedLeafScalarDensity_add]
  exact pairedInverseProfile_integral_add _ hiR hiR' t

/-- Finite scalar source families commute with the actual profile operator
when their literal joint densities are integrable. -/
theorem sourceScalarProfile_finsetSum {I : Type*} (T : Finset I)
    (A : I → (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (k : Mom d)
    (hi : ∀ i ∈ T, Integrable (fun q => maskedLeafScalarDensity hQ hG (A i) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) (t : Fin 2 → ℝ) :
    sourceScalarProfile hQ hG (fun lam β γ z => ∑ i ∈ T, A i lam β γ z) F S t k =
      ∑ i ∈ T, sourceScalarProfile hQ hG (A i) F S t k := by
  classical
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  have he (lam : ℝ × ℝ) (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
      maskedLeafScalarDensity hQ hG (fun lam β γ z => ∑ i ∈ T, A i lam β γ z) F S (lam,p) k =
      ∑ i ∈ T, maskedLeafScalarDensity hQ hG (A i) F S (lam,p) k := by
    simp only [maskedLeafScalarDensity_eq_if]
    split_ifs
    · simp only [Finset.mul_sum]
    · simp only [Finset.sum_const_zero]
  unfold sourceScalarProfile
  simp_rw [he]
  exact pairedInverseProfile_integral_finsetSum _ T _ hi t

end WaveTurbulence.RA1Leafwise

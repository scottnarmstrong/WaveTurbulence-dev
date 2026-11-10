/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarFubini

/-! # Literal source-density support, scalar operations and temporal inversion -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
variable (R R' : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
  (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
variable (F : Mom d → ℂ)
variable (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
  Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- The actual scalar density retains precisely the original support,
root mask, root character, leaf spectrum and scalar source term. -/
theorem maskedLeafScalarDensity_eq_if (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    maskedLeafScalarDensity hQ hG R F S (lam,p) k =
    if p.1.2 ∈ S p.1.1 then sourceRootMask p.1.1 k *
      ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (p.2 a)) k):ℂ)*leafSpectrumCoefficient F p.1.1 p.2 *
        R lam (leafModulations hQ hG p.2).1 (leafModulations hQ hG p.2).2 p.1.2) else 0 := by
  classical
  unfold maskedLeafScalarDensity leafScalarAmplitude maskedModulation
  split_ifs <;> ring

/-- Literal scalar source multiplication is inherited by the complete masked density. -/
theorem maskedLeafScalarDensity_const_mul (c : ℂ) (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    maskedLeafScalarDensity hQ hG (fun lam β γ z => c*R lam β γ z) F S (lam,p) k =
      c*maskedLeafScalarDensity hQ hG R F S (lam,p) k := by
  classical
  simp only [maskedLeafScalarDensity_eq_if]
  split_ifs <;> ring

/-- Literal scalar source addition is inherited by the complete masked density. -/
theorem maskedLeafScalarDensity_add (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    maskedLeafScalarDensity hQ hG (fun lam β γ z => R lam β γ z+R' lam β γ z) F S (lam,p) k =
      maskedLeafScalarDensity hQ hG R F S (lam,p) k+
        maskedLeafScalarDensity hQ hG R' F S (lam,p) k := by
  classical
  simp only [maskedLeafScalarDensity_eq_if]
  split_ifs <;> ring

/-- Temporal inversion retains the same actual support and amplitude;
the original scalar source alone is inverted in time. -/
theorem pairedInverseProfile_maskedLeafScalarDensity (t : Fin 2 → ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    pairedInverseProfile (fun lam => maskedLeafScalarDensity hQ hG R F S (lam,p) k) t =
    if p.1.2 ∈ S p.1.1 then sourceRootMask p.1.1 k *
      ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (p.2 a)) k):ℂ)*leafSpectrumCoefficient F p.1.1 p.2 *
        pairedInverseProfile (fun lam =>
          R lam (leafModulations hQ hG p.2).1 (leafModulations hQ hG p.2).2 p.1.2) t) else 0 := by
  classical
  simp only [maskedLeafScalarDensity_eq_if]
  by_cases hp : p.1.2 ∈ S p.1.1
  · simp only [hp,ite_true]
    simpa only [mul_assoc] using pairedInverseProfile_const_mul
      (sourceRootMask p.1.1 k*(Real.fourierChar (inner ℝ (∑ a, toLp 2 (p.2 a)) k):ℂ)*
        leafSpectrumCoefficient F p.1.1 p.2)
      (fun lam => R lam (leafModulations hQ hG p.2).1 (leafModulations hQ hG p.2).2 p.1.2) t
  · simp only [hp,ite_false,pairedInverseProfile,zero_mul,integral_zero]

end WaveTurbulence.RegAsymp

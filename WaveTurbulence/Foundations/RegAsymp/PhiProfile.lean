/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma58
public import WaveTurbulence.Foundations.ClassJR.MCDefs
public import WaveTurbulence.Foundations.ApproxNT.Statement

/-! # Exact conversion of the J3 special factors to the NT resonant profile

The node sign and the factor pi i are kept outside the scalar energy
cutoffs. No nonzero-energy premise is needed, including on Wick zero planes.
-/

public section
namespace WaveTurbulence.RegAsymp
open ClassJR ApproxNT

/-- The sign in Phi is a constant scalar factor, even at energy zero. -/
theorem phiZ_eq_inverse_sign_mul {ι : Type} (ζ : ι → ℤ) (j : ι)
    (hζ : ζ j = 1 ∨ ζ j = -1) (x : ℝ) :
    PhiZ ζ j x = (((ζ j : ℂ)*Real.pi*Complex.I)⁻¹)*
      ((Fourier.chiInfinity x/x : ℝ):ℂ) := by
  rw [PhiZ,phiR_sign hζ,Complex.ofReal_div]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The special-node product converts exactly to the NT profile. -/
theorem prod_phiZ_mul_eq_resProfile {n : ℕ} (J : Finset (Fin n))
    (ζ : Fin n → ℤ) (hζ : ∀ j ∈ J, ζ j = 1 ∨ ζ j = -1)
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (Ω : Fin n → ℝ) :
    (∏ j ∈ J, PhiZ ζ j (Ω j))*Ψ (WithLp.toLp 2 (fun j => Ω j.val)) =
      (∏ j ∈ J, ((ζ j : ℂ)*Real.pi*Complex.I)⁻¹)*resProfile J Ψ Ω := by
  have he : (∏ j ∈ J, PhiZ ζ j (Ω j)) =
      (∏ j ∈ J, ((ζ j : ℂ)*Real.pi*Complex.I)⁻¹)*
        (∏ j ∈ J, ((Fourier.chiInfinity (Ω j)/(Ω j) : ℝ):ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j hj => phiZ_eq_inverse_sign_mul ζ j (hζ j hj) (Ω j))
  rw [he,resProfile,mul_assoc]

end WaveTurbulence.RegAsymp

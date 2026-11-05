/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.BinaryMomentum

/-! # Scalar homogeneity of the literal source resonant integrals -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

private theorem dslope_const_mul_real (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    dslope (fun t => c*f t) a b = c*dslope f a b := by
  by_cases h : b=a
  · subst b
    rw [dslope_same,dslope_same,deriv_const_mul_field]
  · rw [dslope_of_ne _ h,dslope_of_ne _ h,slope_def_field,slope_def_field]
    ring

/-- The literal momentum-conserving resonant integral is homogeneous,
including the nonintegrable-zero convention of the Bochner integral. -/
theorem resIntegral_const_mul {d : ℕ} (c : ℝ)
    (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    resIntegral (fun k₁ k₂ k₃ => c*Ψ k₁ k₂ k₃) k = c*resIntegral Ψ k := by
  rw [resIntegral,resIntegral,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ℓ
  dsimp only
  rw [integral_const_mul]
  ring

/-- Every literal hyperplane slice is homogeneous without a decay premise. -/
theorem resSlice_const_mul {d : ℕ} (c : ℝ)
    (Ψ : Mom d → Mom d → Mom d → ℝ) (k ℓ : Mom d) (t : ℝ) :
    resSlice (fun k₁ k₂ k₃ => c*Ψ k₁ k₂ k₃) k ℓ t = c*resSlice Ψ k ℓ t := by
  exact integral_const_mul c _

/-- The literal symmetric-quotient resonant integral is homogeneous.
This uses its defined quotient formula rather than unrestricted limUnder linearity. -/
theorem pvResonantIntegral_const_mul {d : ℕ} (c : ℝ)
    (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    pvResonantIntegral (fun k₁ k₂ k₃ => c*Ψ k₁ k₂ k₃) k = c*pvResonantIntegral Ψ k := by
  rw [pvResonantIntegral,pvResonantIntegral,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ℓ
  dsimp only
  have he : (fun v => resSlice (fun k₁ k₂ k₃ => c*Ψ k₁ k₂ k₃) k ℓ v -
      resSlice (fun k₁ k₂ k₃ => c*Ψ k₁ k₂ k₃) k ℓ (-v)) =
      (fun v => c*(resSlice Ψ k ℓ v-resSlice Ψ k ℓ (-v))) := by
    funext v
    rw [resSlice_const_mul,resSlice_const_mul,mul_sub]
  rw [he]
  simp only [dslope_const_mul_real]
  have hi : (fun t : ℝ => (2:ℝ)⁻¹*(c*dslope
      (fun v => resSlice Ψ k ℓ v-resSlice Ψ k ℓ (-v)) 0 t)) =
      (fun t => c*((2:ℝ)⁻¹*dslope
        (fun v => resSlice Ψ k ℓ v-resSlice Ψ k ℓ (-v)) 0 t)) := by
    funext t
    ring
  rw [hi,integral_const_mul]
  ring

/-- Scaling the two actual child functions scales their binary kernel
by the product, for all three missing-child alternatives. -/
theorem binaryMomentumFunction_const_mul {d : ℕ} (j : Fin 3) (a b : ℝ)
    (f g : Mom d → ℝ) :
    binaryMomentumFunction j (fun k => a*f k) (fun k => b*g k) =
      fun k₁ k₂ k₃ => (a*b)*binaryMomentumFunction j f g k₁ k₂ k₃ := by
  funext k₁ k₂ k₃
  fin_cases j
  · change (a*f k₂)*(b*g k₃) = (a*b)*(f k₂*g k₃)
    ring
  · change (a*f k₁)*(b*g k₃) = (a*b)*(f k₁*g k₃)
    ring
  · change (a*f k₁)*(b*g k₂) = (a*b)*(f k₁*g k₂)
    ring

end WaveTurbulence.RegAsymp

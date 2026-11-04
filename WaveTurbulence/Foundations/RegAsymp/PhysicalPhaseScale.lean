/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.Normalization
public import WaveTurbulence.Foundations.ApproxNT.AppRep

/-! # Exact normalization for the physical energy Ω = 2⟨x,y⟩

The number-theory parameter is 2δ, while the source coupling retains δ.
Both effects are kept explicitly before the momentum-factor identification.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

/-- Rescaling the NT parameter does not rescale the source coupling. -/
theorem physical_prefactor_rescale (n : ℕ) (X δ : ℝ) (z : ℂ) :
    (((δ/(2*X))^(2*n):ℝ):ℂ)*z =
      (1/2:ℂ)^(2*n)*((((2*δ/(2*X))^(2*n):ℝ):ℂ)*z) := by
  have hh : δ/(2*X) = (1/2:ℝ)*(2*δ/(2*X)) := by ring
  rw [hh,mul_pow,Complex.ofReal_mul]
  push_cast
  ring

/-- The exact leading coefficient for the physical phase. A later bridge
identifies the singular integral, including its factor2 per energy variable,
with the source momentum factor. -/
theorem physical_normalized_app {d n : ℕ} {L δ γ : ℝ} (hL : 0 < L) (hδ : δ ≠ 0)
    (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*approxApp L (2*δ) γ J Ψ W =
      (((δ/8)^n:ℝ):ℂ)*(∫ Ω, Ψ Ω)*singInt J W := by
  have hh := scaled_normalization_identity n
    (ne_of_gt (Real.rpow_pos_of_pos hL ((d:ℝ)-γ))) hδ (by norm_num : (2:ℝ) ≠ 0) (1:ℝ)
  rw [← lattice_scale_square hL d γ,one_mul] at hh
  norm_num only [mul_one,show (4:ℝ)*2=8 by norm_num] at hh
  unfold approxApp
  rw [← mul_assoc,← mul_assoc,← Complex.ofReal_pow,← Complex.ofReal_mul,hh,one_mul]

end WaveTurbulence.RegAsymp

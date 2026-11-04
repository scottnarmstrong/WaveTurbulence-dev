/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WKE.CollisionOp

/-! # Decay classes for the three binary resonant products in Nstar -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

variable {d : ℕ}

/-- The missing-child alternatives in TARGET (regref3-4), in the original
momentum-conserving parametrization (k+ell,k+ell+x,k+x). -/
def binaryResonantKernel (j : Fin 3) (f g : Mom d → ℝ) (k ℓ x : Mom d) : ℝ :=
  match j with
  | 0 => f (k+ℓ+x)*g (k+x)
  | 1 => f (k+ℓ)*g (k+x)
  | _ => f (k+ℓ)*g (k+ℓ+x)

/-- The outer integrable weight for the original binary product. -/
def binaryResonantWeight (j : Fin 3) (C N : ℝ) (k ℓ : Mom d) : ℝ :=
  if j=0 then C^2*(1+‖ℓ‖)^(-(N/2)) else C^2*(1+‖k+ℓ‖)^(-(N/2))

/-- The actual translation center of the remaining integration variable. -/
def binaryResonantShift (j : Fin 3) (k ℓ : Mom d) : Mom d :=
  if j=2 then k+ℓ else k

/-- Each binary source product has precisely the same polynomial decay
class as the landed cubic collision kernels, without adding a fictitious
third decaying child. -/
theorem deltaKernel_binaryResonant {C N : ℝ} (hd : 2 ≤ d) (hN : 2*(d:ℝ) < N)
    {f g : Mom d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfb : DecayBound C N f) (hgb : DecayBound C N g) (j : Fin 3) (k : Mom d) :
    DeltaKernel (binaryResonantKernel j f g k)
      (binaryResonantWeight j C N k) (binaryResonantShift j k) (N/2) := by
  have hN0 : 0 ≤ N := by have hdim : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d; linarith
  have hNhalf : (d:ℝ) < N/2 := by linarith
  have hC : 0 ≤ C := hfb.C_nonneg
  have hh (x : Mom d) : (1+‖x‖)^(-N) ≤ (1+‖x‖)^(-(N/2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (by linarith)
  have hfb' (x : Mom d) : |f x| ≤ C*(1+‖x‖)^(-(N/2)) :=
    (hfb x).trans (mul_le_mul_of_nonneg_left (hh x) hC)
  have hgb' (x : Mom d) : |g x| ≤ C*(1+‖x‖)^(-(N/2)) :=
    (hgb x).trans (mul_le_mul_of_nonneg_left (hh x) hC)
  refine ⟨?_,?_,hNhalf,?_⟩
  · fin_cases j
    all_goals exact (hf.comp (by fun_prop)).mul (hg.comp (by fun_prop))
  · intro ℓ x
    fin_cases j
    · change |f (k+ℓ+x)*g (k+x)| ≤ C^2*(1+‖ℓ‖)^(-(N/2))*(1+‖k+x‖)^(-(N/2))
      rw [abs_mul]
      have hp := one_add_norm_rpow_neg_mul_le (k+x) ℓ hN0
      rw [show k+x+ℓ = k+ℓ+x by abel] at hp
      calc
        _ ≤ (C*(1+‖k+ℓ+x‖)^(-N))*(C*(1+‖k+x‖)^(-N)) :=
          mul_le_mul (hfb _) (hgb _) (abs_nonneg _) (by positivity)
        _ = C^2*((1+‖k+ℓ+x‖)^(-N)*(1+‖k+x‖)^(-N)) := by ring
        _ ≤ C^2*((1+‖ℓ‖)^(-(N/2))*(1+‖k+x‖)^(-(N/2))) :=
          mul_le_mul_of_nonneg_left hp (sq_nonneg C)
        _ = _ := by ring
    · change |f (k+ℓ)*g (k+x)| ≤ C^2*(1+‖k+ℓ‖)^(-(N/2))*(1+‖k+x‖)^(-(N/2))
      rw [abs_mul]
      calc
        _ ≤ (C*(1+‖k+ℓ‖)^(-(N/2)))*(C*(1+‖k+x‖)^(-(N/2))) :=
          mul_le_mul (hfb' _) (hgb' _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · change |f (k+ℓ)*g (k+ℓ+x)| ≤ C^2*(1+‖k+ℓ‖)^(-(N/2))*(1+‖k+ℓ+x‖)^(-(N/2))
      rw [abs_mul]
      calc
        _ ≤ (C*(1+‖k+ℓ‖)^(-(N/2)))*(C*(1+‖k+ℓ+x‖)^(-(N/2))) :=
          mul_le_mul (hfb' _) (hgb' _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
  · by_cases hj : j=0
    · subst j
      simpa only [binaryResonantWeight,ite_true,zero_add,mul_left_comm] using
        (integrable_inv_norm_mul_one_add_norm hd hNhalf (0:Mom d)).const_mul (C^2)
    · simpa only [binaryResonantWeight,hj,ite_false,mul_left_comm] using
        (integrable_inv_norm_mul_one_add_norm hd hNhalf k).const_mul (C^2)

end WaveTurbulence.RegAsymp

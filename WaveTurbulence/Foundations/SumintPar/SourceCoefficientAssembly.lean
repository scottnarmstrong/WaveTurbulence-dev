/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormalizedSourceCoefficient
public import WaveTurbulence.Foundations.SumintPar.SmallParameterConditions

/-!
# Step-independent constants for the final source estimate

The Fourier coefficient base depends only on dimension and A. The
assembly constant also contains the actual interpolated kernel constant,
which is chosen before delta and the step count.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.SumintPar

/-- The exact total normalized spatial Fourier coefficient base. -/
@[expose] noncomputable def sourceCoefficientBase (d : ℕ) (A : ℝ) : ℝ :=
  ((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d

/-- The source coefficient base is nonnegative under the drafted A assumption. -/
theorem sourceCoefficientBase_nonneg (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 ≤ sourceCoefficientBase d A :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hA) _))
    (summedCellFourierFactor_nonneg _ _)) (cellFourierFactor_nonneg _)

/-- The final fixed assembly constant; it has no delta or step-count dependence. -/
@[expose] noncomputable def sourceAssemblyConstant (d : ℕ) (A G : ℝ) : ℝ :=
  max 8 (2*max 1 (sourceCoefficientBase d A)*G)

/-- The final fixed assembly constant is at least one. -/
theorem one_le_sourceAssemblyConstant (d : ℕ) (A G : ℝ) : 1 ≤ sourceAssemblyConstant d A G :=
  (by norm_num : (1:ℝ) ≤ 8).trans (le_max_left _ _)

/-- The elementary modulation and coefficient factors fit in the source fixed constant. -/
theorem source_coefficient_modulation_budget {S G P θ s : ℝ} (hS : 0 ≤ S) (hG : 1 ≤ G)
    (hP : 1 ≤ P) (hθ : θ ∈ Set.Icc (0:ℝ) 1) (hθs : θ ≤ s) (m : ℕ)
    {C : ℝ} (hC8 : 8 ≤ C) (hCbase : 2*S*G ≤ C) :
    S^m*2^θ*(((m:ℝ)+1)*P)^θ*4^θ*G^m ≤ C*P^s*C^m := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hM : 1 ≤ (m:ℝ)+1 := by linarith only [show (0:ℝ) ≤ m from Nat.cast_nonneg m]
  have hM2 : (m:ℝ)+1 ≤ (2:ℝ)^m := by
    exact_mod_cast (show m+1 ≤ 2^m from Nat.succ_le_iff.mpr Nat.lt_two_pow_self)
  have h2 : (2:ℝ)^θ ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hθ.2
  have h4 : (4:ℝ)^θ ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hθ.2
  have hMP : (((m:ℝ)+1)*P)^θ ≤ (2:ℝ)^m*P^s := by
    rw [Real.mul_rpow (by positivity) hP0]
    apply mul_le_mul
    · have hmθ : ((m:ℝ)+1)^θ ≤ (m:ℝ)+1 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM hθ.2
      exact hmθ.trans hM2
    · exact Real.rpow_le_rpow_of_exponent_le hP hθs
    · positivity
    · positivity
  have hmod : 2^θ*(((m:ℝ)+1)*P)^θ*4^θ ≤ 8*(2:ℝ)^m*P^s := by
    have hh := mul_le_mul (mul_le_mul h2 hMP (by positivity) (by norm_num)) h4 (by positivity) (by positivity)
    convert hh using 1; ring
  calc
    _ = (S*G)^m*(2^θ*(((m:ℝ)+1)*P)^θ*4^θ) := by rw [mul_pow]; ring
    _ ≤ (S*G)^m*(8*(2:ℝ)^m*P^s) := mul_le_mul_of_nonneg_left hmod (pow_nonneg (mul_nonneg hS hG0) _)
    _ = 8*P^s*(2*S*G)^m := by simp only [mul_pow]; ring
    _ ≤ C*P^s*C^m := mul_le_mul
      (mul_le_mul_of_nonneg_right hC8 (by positivity))
      (pow_le_pow_left₀ (by positivity) hCbase _) (by positivity) (by positivity)

end WaveTurbulence.SumintPar

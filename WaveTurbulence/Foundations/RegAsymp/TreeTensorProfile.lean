/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreePolynomialProfile
public import WaveTurbulence.Foundations.ClassJR.KernelM
public import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Tensor Fourier profiles for the source tree time polynomial -/

public section
noncomputable section
open scoped ContDiff ENNReal
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- Fixed cutoff monomial on the source time interval. -/
@[expose] def treeTimeMonomial (n : ℕ) (t : ℝ) : ℂ := (t : ℂ)^n * psi0 t

/-- Its actual Fourier transform, with the source π normalization. -/
@[expose] def treeTimeMonomialProfile (n : ℕ) : ℝ → ℂ := ftπ (treeTimeMonomial n)

theorem contDiff_treeTimeMonomial (n : ℕ) : ContDiff ℝ ∞ (treeTimeMonomial n) :=
  (Complex.ofRealCLM.contDiff.pow n).mul contDiff_psi0

theorem hasCompactSupport_treeTimeMonomial (n : ℕ) :
    HasCompactSupport (treeTimeMonomial n) := hasCompactSupport_psi0.mul_left

theorem integrable_treeTimeMonomialProfile (n : ℕ) : Integrable (treeTimeMonomialProfile n) :=
  integrable_ftπ (contDiff_treeTimeMonomial n) (hasCompactSupport_treeTimeMonomial n)

/-- Exact tensor inversion; no time-ordering extension is imposed. -/
theorem integral_treeTimeMonomialProfile (a b : ℕ) (t s : ℝ) :
    (∫ lam : ℝ × ℝ, treeTimeMonomialProfile a lam.1 *
      treeTimeMonomialProfile b lam.2 * e2 lam t s) =
      treeTimeMonomial a t * treeTimeMonomial b s := by
  simp_rw [e2_split]
  have h : ∀ lam : ℝ × ℝ,
      treeTimeMonomialProfile a lam.1 * treeTimeMonomialProfile b lam.2 *
        (Complex.exp (Real.pi * Complex.I * (lam.1 * t)) *
          Complex.exp (Real.pi * Complex.I * (lam.2 * s))) =
      (treeTimeMonomialProfile a lam.1 * Complex.exp (Real.pi * Complex.I * lam.1 * t)) *
      (treeTimeMonomialProfile b lam.2 * Complex.exp (Real.pi * Complex.I * lam.2 * s)) := by
    intro lam
    simp only [mul_assoc]
    ring
  simp_rw [h]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (fun x : ℝ => treeTimeMonomialProfile a x * Complex.exp (Real.pi * Complex.I * x * t))
    (fun x : ℝ => treeTimeMonomialProfile b x * Complex.exp (Real.pi * Complex.I * x * s))]
  exact congrArg₂ (fun x y : ℂ => x*y)
    (integral_ftπ_mul_exp (contDiff_treeTimeMonomial a) (hasCompactSupport_treeTimeMonomial a) t)
    (integral_ftπ_mul_exp (contDiff_treeTimeMonomial b) (hasCompactSupport_treeTimeMonomial b) s)

/-- On the source square, tensor inversion gives the unmodified monomial. -/
theorem integral_treeTimeMonomialProfile_on_square (a b : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    (∫ lam : ℝ × ℝ, treeTimeMonomialProfile a lam.1 *
      treeTimeMonomialProfile b lam.2 * e2 lam t s) = (t:ℂ)^a * (s:ℂ)^b := by
  rw [integral_treeTimeMonomialProfile]
  simp only [treeTimeMonomial, psi0_eq_one ht, psi0_eq_one hs, mul_one]

/-- For subunit exponents the time weight is bounded by the tensor linear weight. -/
theorem tree_wL_le_product {θ : ℝ} (hθ : θ ≤ 1) (lam : ℝ × ℝ) :
    wL θ lam ≤ (1 + ‖lam.1‖ₑ) * (1 + ‖lam.2‖ₑ) := by
  calc
    _ ≤ 1 + ‖lam.1‖ₑ + ‖lam.2‖ₑ := by
      unfold wL
      exact (ENNReal.rpow_le_rpow_of_exponent_le
        (le_add_right (le_add_right le_rfl)) hθ).trans_eq (ENNReal.rpow_one _)
    _ ≤ 1 + ‖lam.1‖ₑ + ‖lam.2‖ₑ + ‖lam.1‖ₑ * ‖lam.2‖ₑ := le_add_right le_rfl
    _ = _ := by ring

/-- The linear weighted scalar profile has a geometric integrable majorant. -/
theorem tree_weighted_scalar_bound {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hb : ∀ n ξ, ‖treeTimeMonomialProfile n ξ‖ ≤ K * B^n / (1 + |ξ|)^3)
    (n : ℕ) (ξ : ℝ) :
    (1 + ‖ξ‖ₑ) * ‖treeTimeMonomialProfile n ξ‖ₑ ≤
      ENNReal.ofReal (K * B^n) * ENNReal.ofReal ((1 + |ξ|)^(-(2:ℝ))) := by
  have hKB : 0 ≤ K * B^n := mul_nonneg hK (pow_nonneg hB _)
  rw [show (1:ℝ≥0∞) + ‖ξ‖ₑ = ENNReal.ofReal (1 + |ξ|) by
    rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one,
      ← Real.norm_eq_abs, ofReal_norm], ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hKB]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 < 1 + |ξ| := by positivity
  have he : (1 + |ξ|)^(-(2:ℝ)) = (1 + |ξ|) * ((1 + |ξ|)^3)⁻¹ := by
    rw [Real.rpow_neg hp.le, show (1 + |ξ|)^(2:ℝ) = (1 + |ξ|)^(2:ℕ) by norm_cast]
    field_simp
  rw [he]
  calc
    _ ≤ (1 + |ξ|) * (K * B^n / (1 + |ξ|)^3) :=
      mul_le_mul_of_nonneg_left (hb n ξ) hp.le
    _ = _ := by ring

/-- A single geometric constant bounds all tensor profile masses, uniformly for θ≤1. -/
theorem exists_tree_tensor_profile_mass : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
    ∀ (a b : ℕ) (θ : ℝ), θ ≤ 1 →
      (∫⁻ lam : ℝ × ℝ, wL θ lam *
        ‖treeTimeMonomialProfile a lam.1 * treeTimeMonomialProfile b lam.2‖ₑ) ≤
        ENNReal.ofReal (K * B^(a+b)) := by
  obtain ⟨K, B, hK, hB, hb⟩ :=
    exists_norm_ftpi_monomial_le contDiff_psi0 hasCompactSupport_psi0
  refine ⟨(K * Ir 2)^2, B, sq_nonneg _, hB, ?_⟩
  intro a b θ hθ
  let D : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + |x|)^(-(2:ℝ)))
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hpoint (lam : ℝ × ℝ) : wL θ lam *
      ‖treeTimeMonomialProfile a lam.1 * treeTimeMonomialProfile b lam.2‖ₑ ≤
      (ENNReal.ofReal (K*B^a) * ENNReal.ofReal (K*B^b)) * (D lam.1 * D lam.2) := by
    rw [enorm_mul]
    calc
      _ ≤ ((1 + ‖lam.1‖ₑ) * (1 + ‖lam.2‖ₑ)) *
          (‖treeTimeMonomialProfile a lam.1‖ₑ * ‖treeTimeMonomialProfile b lam.2‖ₑ) :=
        mul_le_mul' (tree_wL_le_product hθ lam) le_rfl
      _ = ((1 + ‖lam.1‖ₑ) * ‖treeTimeMonomialProfile a lam.1‖ₑ) *
          ((1 + ‖lam.2‖ₑ) * ‖treeTimeMonomialProfile b lam.2‖ₑ) := by ring
      _ ≤ (ENNReal.ofReal (K*B^a) * D lam.1) * (ENNReal.ofReal (K*B^b) * D lam.2) :=
        mul_le_mul' (tree_weighted_scalar_bound hK hB hb a lam.1)
          (tree_weighted_scalar_bound hK hB hb b lam.2)
      _ = _ := by ring
  apply (lintegral_mono hpoint).trans
  rw [lintegral_const_mul _ (by fun_prop), Measure.volume_eq_prod,
    lintegral_prod_mul hD.aemeasurable hD.aemeasurable]
  have hi : ∫⁻ x, D x = ENNReal.ofReal (Ir 2) := lintegral_Ir_eq (by norm_num)
  rw [hi]
  rw [← ENNReal.ofReal_mul (show 0 ≤ Ir 2 from ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_mul (mul_nonneg hK (pow_nonneg hB _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hK (pow_nonneg hB _))
      (mul_nonneg hK (pow_nonneg hB _)))]
  apply le_of_eq
  congr 1
  rw [pow_add]
  ring

end WaveTurbulence.RegAsymp

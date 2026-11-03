/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polynomial moments of two independent real Gaussians

The integration-by-parts proof of the mixed-moment identity used in DH21 Lemma A.2.
The scalar recursion is mined from `RegularityStructures.BPHZ.GaussianPolynomialIBP`,
with the variance changed to `1 / 2` and the integration-by-parts hypotheses discharged here.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace WaveTurbulence.ComplexGaussianPolynomial

private lemma integrable_halfGaussian_weight {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 (1 / 2))) :
    Integrable (fun x => f x * gaussianPDFReal 0 (1 / 2) x) := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)] at hf
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using hf

private lemma hasDerivAt_halfGaussian_density (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 (1 / 2))
      (-2 * x * gaussianPDFReal 0 (1 / 2) x) x := by
  have hpdf : gaussianPDFReal 0 (1 / 2) =
      fun y : ℝ => (Real.sqrt Real.pi)⁻¹ * Real.exp (-y ^ 2) := by
    funext y
    rw [gaussianPDFReal_def]
    have hden : (2 : ℝ) * Real.pi * (↑(1 / 2 : ℝ≥0)) = Real.pi := by norm_num; ring
    rw [hden]
    norm_num
  rw [hpdf]
  have harg : HasDerivAt (fun y : ℝ => -y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_pow 2 x).neg using 1; simp
  convert harg.exp.const_mul (Real.sqrt Real.pi)⁻¹ using 1; ring

lemma integral_pow_succ_halfGaussian (a : ℕ) :
    ∫ x : ℝ, x ^ (a + 1) ∂gaussianReal 0 (1 / 2) =
      (a : ℝ) / 2 * ∫ x : ℝ, x ^ (a - 1) ∂gaussianReal 0 (1 / 2) := by
  have hint (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 (1 / 2)) := by
    exact integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) n
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ a) (u' := fun x => (a : ℝ) * x ^ (a - 1))
    (v := gaussianPDFReal 0 (1 / 2))
    (v' := fun x => -2 * x * gaussianPDFReal 0 (1 / 2) x)
    (fun x _ => hasDerivAt_pow a x)
    (fun x _ => hasDerivAt_halfGaussian_density x)
    (by
      have h := (integrable_halfGaussian_weight (hint (a + 1))).const_mul (-2)
      convert h using 1
      ext x
      simp only [Pi.mul_apply, pow_succ]
      ring)
    (integrable_halfGaussian_weight ((hint (a - 1)).const_mul a))
    (integrable_halfGaussian_weight (hint a))
  have he (x : ℝ) : x ^ a * (-2 * x * gaussianPDFReal 0 (1 / 2) x) =
      -2 * (gaussianPDFReal 0 (1 / 2) x * x ^ (a + 1)) := by rw [pow_succ]; ring
  simp_rw [he] at hparts
  rw [integral_const_mul] at hparts
  have he' (x : ℝ) : (a : ℝ) * x ^ (a - 1) * gaussianPDFReal 0 (1 / 2) x =
      a * (gaussianPDFReal 0 (1 / 2) x * x ^ (a - 1)) := by ring
  simp_rw [he'] at hparts
  rw [integral_const_mul] at hparts
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  linarith only [hparts]

open MvPolynomial
open scoped BigOperators

private lemma integral_complex_pow_halfGaussian (a : ℕ) :
    ∫ x : ℝ, (x : ℂ) ^ a ∂gaussianReal 0 (1 / 2) =
      Complex.ofReal (∫ x : ℝ, x ^ a ∂gaussianReal 0 (1 / 2)) := by
  simp only [← Complex.ofReal_pow, integral_complex_ofReal]

private lemma integrable_complex_pow_halfGaussian (a : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ a) (gaussianReal 0 (1 / 2)) := by
  have h : Integrable (fun x : ℝ => x ^ a) (gaussianReal 0 (1 / 2)) :=
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) a
  apply (h.ofReal (𝕜 := ℂ)).congr
  exact Filter.Eventually.of_forall fun x => Complex.ofReal_pow x a

private lemma eval_pair_monomial (s : Fin 2 →₀ ℕ) (c : ℂ) (x : ℝ × ℝ) :
    eval (fun i : Fin 2 => if i = 0 then (x.1 : ℂ) else (x.2 : ℂ)) (monomial s c) =
      c * (x.1 : ℂ) ^ s 0 * (x.2 : ℂ) ^ s 1 := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  norm_num
  ring

lemma integrable_eval_pair_halfGaussian (p : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun x : ℝ × ℝ =>
      eval (fun i : Fin 2 => if i = 0 then (x.1 : ℂ) else (x.2 : ℂ)) p)
      ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    simp_rw [eval_pair_monomial, mul_assoc]
    exact ((integrable_complex_pow_halfGaussian (s 0)).mul_prod
      (integrable_complex_pow_halfGaussian (s 1))).const_mul c
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq

private lemma integral_eval_pair_monomial (s : Fin 2 →₀ ℕ) (c : ℂ) :
    (∫ x : ℝ × ℝ,
      eval (fun i : Fin 2 => if i = 0 then (x.1 : ℂ) else (x.2 : ℂ)) (monomial s c)
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) =
      c * Complex.ofReal (∫ x : ℝ, x ^ s 0 ∂gaussianReal 0 (1 / 2)) *
        Complex.ofReal (∫ x : ℝ, x ^ s 1 ∂gaussianReal 0 (1 / 2)) := by
  simp_rw [eval_pair_monomial, mul_assoc]
  rw [integral_const_mul]
  rw [integral_prod_mul (fun x : ℝ => (x : ℂ) ^ s 0) (fun x : ℝ => (x : ℂ) ^ s 1)]
  rw [integral_complex_pow_halfGaussian, integral_complex_pow_halfGaussian]


open MvPolynomial

lemma integral_eval_pair_X_mul (i : Fin 2) (p : MvPolynomial (Fin 2) ℂ) :
    (∫ x : ℝ × ℝ,
      eval (fun j : Fin 2 => if j = 0 then (x.1 : ℂ) else (x.2 : ℂ)) (X i * p)
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) =
      (1 / 2 : ℂ) * ∫ x : ℝ × ℝ,
        eval (fun j : Fin 2 => if j = 0 then (x.1 : ℂ) else (x.2 : ℂ)) (pderiv i p)
        ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    have hm : X i * monomial s c = monomial (Finsupp.single i 1 + s) c := by
      rw [monomial_single_add, pow_one]
    rw [hm, pderiv_monomial, integral_eval_pair_monomial,
      integral_eval_pair_monomial]
    fin_cases i <;>
      norm_num [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Nat.add_comm] <;>
      rw [Nat.add_comm 1, integral_pow_succ_halfGaussian] <;> push_cast <;> ring
  | add p q hp hq =>
    simp only [mul_add, map_add]
    rw [integral_add (integrable_eval_pair_halfGaussian _) (integrable_eval_pair_halfGaussian _),
      integral_add (integrable_eval_pair_halfGaussian _) (integrable_eval_pair_halfGaussian _),
      hp, hq, mul_add]

open MvPolynomial

/-- Expectation of a polynomial of independent real `N(0, 1/2)` coordinates. -/
@[expose] noncomputable def expectation : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun p := ∫ x : ℝ × ℝ,
    eval (fun j : Fin 2 => if j = 0 then (x.1 : ℂ) else (x.2 : ℂ)) p
    ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))
  map_add' p q := by
    simp only [map_add]
    exact integral_add (integrable_eval_pair_halfGaussian p) (integrable_eval_pair_halfGaussian q)
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul, integral_const_mul, RingHom.id_apply]

/-- The complex coordinate `x + iy`, as a polynomial in two real coordinates. -/
@[expose] noncomputable def coordinate : MvPolynomial (Fin 2) ℂ := X 0 + C Complex.I * X 1
/-- The conjugate coordinate `x - iy`. -/
@[expose] noncomputable def conjugateCoordinate : MvPolynomial (Fin 2) ℂ := X 0 - C Complex.I * X 1

lemma expectation_C_mul (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) :
    expectation (C c * p) = c * expectation p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

lemma expectation_Z_mul (p : MvPolynomial (Fin 2) ℂ) :
    expectation (coordinate * p) =
      (1 / 2 : ℂ) * expectation (pderiv 0 p) +
        Complex.I / 2 * expectation (pderiv 1 p) := by
  simp only [coordinate, add_mul, mul_assoc, map_add, expectation_C_mul]
  change (∫ x : ℝ × ℝ, eval _ (X 0 * p) ∂_) +
    Complex.I * (∫ x : ℝ × ℝ, eval _ (X 1 * p) ∂_) = _
  rw [integral_eval_pair_X_mul, integral_eval_pair_X_mul]
  simp only [expectation, LinearMap.coe_mk, AddHom.coe_mk]
  ring

lemma expectation_W_mul (p : MvPolynomial (Fin 2) ℂ) :
    expectation (conjugateCoordinate * p) =
      (1 / 2 : ℂ) * expectation (pderiv 0 p) -
        Complex.I / 2 * expectation (pderiv 1 p) := by
  simp only [conjugateCoordinate, sub_mul, mul_assoc, map_sub, expectation_C_mul]
  change (∫ x : ℝ × ℝ, eval _ (X 0 * p) ∂_) -
    Complex.I * (∫ x : ℝ × ℝ, eval _ (X 1 * p) ∂_) = _
  rw [integral_eval_pair_X_mul, integral_eval_pair_X_mul]
  simp only [expectation, LinearMap.coe_mk, AddHom.coe_mk]
  ring

lemma pderiv_coordinate (i : Fin 2) :
    pderiv i coordinate = if i = 0 then 1 else C Complex.I := by
  fin_cases i <;> simp [coordinate, pderiv_X]

lemma pderiv_conjugateCoordinate (i : Fin 2) :
    pderiv i conjugateCoordinate = if i = 0 then 1 else -C Complex.I := by
  fin_cases i <;> simp [conjugateCoordinate, pderiv_X]

lemma expectation_monomial_Z_succ (a b : ℕ) :
    expectation (coordinate ^ (a + 1) * conjugateCoordinate ^ b) =
      (b : ℂ) * expectation (coordinate ^ a * conjugateCoordinate ^ (b - 1)) := by
  rw [pow_succ', mul_assoc, expectation_Z_mul]
  have hc (n : ℕ) : (n : MvPolynomial (Fin 2) ℂ) = C (n : ℂ) := by simp
  have h0 : pderiv 0 (coordinate ^ a * conjugateCoordinate ^ b) =
      C (a : ℂ) * (coordinate ^ (a - 1) * conjugateCoordinate ^ b) +
        C (b : ℂ) * (coordinate ^ a * conjugateCoordinate ^ (b - 1)) := by
    simp only [pderiv_mul, pderiv_pow, pderiv_coordinate, pderiv_conjugateCoordinate, hc]
    norm_num
    ring
  have h1 : pderiv 1 (coordinate ^ a * conjugateCoordinate ^ b) =
      C Complex.I * (C (a : ℂ) * (coordinate ^ (a - 1) * conjugateCoordinate ^ b) -
        C (b : ℂ) * (coordinate ^ a * conjugateCoordinate ^ (b - 1))) := by
    simp only [pderiv_mul, pderiv_pow, pderiv_coordinate, pderiv_conjugateCoordinate, hc]
    norm_num
    ring
  rw [h0, h1]
  simp only [map_add, map_sub, expectation_C_mul]
  have hi := Complex.I_sq
  linear_combination (expectation (coordinate ^ (a - 1) * conjugateCoordinate ^ b) * a / 2 -
    expectation (coordinate ^ a * conjugateCoordinate ^ (b - 1)) * b / 2) * hi

lemma expectation_monomial_W_succ (a b : ℕ) :
    expectation (coordinate ^ a * conjugateCoordinate ^ (b + 1)) =
      (a : ℂ) * expectation (coordinate ^ (a - 1) * conjugateCoordinate ^ b) := by
  rw [pow_succ' conjugateCoordinate, ← mul_assoc, mul_comm (coordinate ^ a) conjugateCoordinate,
    mul_assoc, expectation_W_mul]
  have hc (n : ℕ) : (n : MvPolynomial (Fin 2) ℂ) = C (n : ℂ) := by simp
  have h0 : pderiv 0 (coordinate ^ a * conjugateCoordinate ^ b) =
      C (a : ℂ) * (coordinate ^ (a - 1) * conjugateCoordinate ^ b) +
        C (b : ℂ) * (coordinate ^ a * conjugateCoordinate ^ (b - 1)) := by
    simp only [pderiv_mul, pderiv_pow, pderiv_coordinate, pderiv_conjugateCoordinate, hc]
    norm_num
    ring
  have h1 : pderiv 1 (coordinate ^ a * conjugateCoordinate ^ b) =
      C Complex.I * (C (a : ℂ) * (coordinate ^ (a - 1) * conjugateCoordinate ^ b) -
        C (b : ℂ) * (coordinate ^ a * conjugateCoordinate ^ (b - 1))) := by
    simp only [pderiv_mul, pderiv_pow, pderiv_coordinate, pderiv_conjugateCoordinate, hc]
    norm_num
    ring
  rw [h0, h1]
  simp only [map_add, map_sub, expectation_C_mul]
  have hi := Complex.I_sq
  linear_combination (-expectation (coordinate ^ (a - 1) * conjugateCoordinate ^ b) * a / 2 +
    expectation (coordinate ^ a * conjugateCoordinate ^ (b - 1)) * b / 2) * hi


lemma expectation_one : expectation 1 = 1 := by
  simp [expectation]

lemma expectation_mixed (a b : ℕ) :
    expectation (coordinate ^ a * conjugateCoordinate ^ b) =
      if a = b then (a.factorial : ℂ) else 0 := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simp [expectation_one]
    | succ b =>
      rw [expectation_monomial_W_succ]
      simp
  | succ a ih =>
    cases b with
    | zero =>
      rw [expectation_monomial_Z_succ]
      simp
    | succ b =>
      rw [expectation_monomial_Z_succ, Nat.add_sub_cancel, ih]
      by_cases h : a = b
      · subst b
        simp [Nat.factorial_succ]
      · simp [h]
end WaveTurbulence.ComplexGaussianPolynomial

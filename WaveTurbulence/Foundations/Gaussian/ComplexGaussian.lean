/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
import WaveTurbulence.Foundations.Gaussian.IsserlisPolynomial
public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Normalized complex Gaussian law

The normalization in DH21 Lemma A.2 is realized by independent real and imaginary
parts of variance `1 / 2`. The coordinate construction uses `Measure.infinitePi`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace WaveTurbulence

private theorem measurable_complexFromPair : Measurable Complex.equivRealProd.symm :=
  Complex.equivRealProdCLM.symm.continuous.measurable

instance : IsProbabilityMeasure stdComplexGaussian := by
  unfold stdComplexGaussian
  infer_instance

/-- Coordinates on the canonical product space have the normalized complex Gaussian law. -/
theorem hasLaw_stdComplexGaussian_eval {ι : Type*} (i : ι) :
    HasLaw (fun ω : ι → ℂ => ω i) stdComplexGaussian
      (Measure.infinitePi (fun _ : ι => stdComplexGaussian)) :=
  (measurePreserving_eval_infinitePi (fun _ : ι => stdComplexGaussian) i).hasLaw

/-- The canonical complex Gaussian coordinates are mutually independent, even without
countability of the index type. -/
theorem iIndepFun_stdComplexGaussian_eval {ι : Type*} :
    iIndepFun (fun i (ω : ι → ℂ) => ω i)
      (Measure.infinitePi (fun _ : ι => stdComplexGaussian)) :=
  iIndepFun_infinitePi (X := fun (_ : ι) (z : ℂ) => z) (fun _ => measurable_id)

/-- Every finite absolute moment of the normalized complex Gaussian is finite. -/
theorem memLp_id_stdComplexGaussian (p : ℝ≥0) :
    MemLp (fun z : ℂ => z) p stdComplexGaussian := by
  rw [stdComplexGaussian, memLp_map_measure_iff (by fun_prop)
    measurable_complexFromPair.aemeasurable]
  have h := memLp_id_gaussianReal (μ := 0) (v := 1 / 2) p
  have hre := (h.comp_fst (gaussianReal 0 (1 / 2))).ofReal (K := ℂ)
  have him := (h.comp_snd (gaussianReal 0 (1 / 2))).ofReal (K := ℂ)
  convert hre.add (him.mul_const Complex.I) using 1
  ext x
  simp only [Function.comp_def, id_eq, Pi.add_apply, Complex.equivRealProd_symm_apply]
  norm_num [Complex.ext_iff]

/-- All mixed holomorphic and antiholomorphic monomials are integrable (DH21 Lemma A.2). -/
theorem integrable_monomial_stdComplexGaussian (a b : ℕ) :
    Integrable (fun z : ℂ => z ^ a * star z ^ b) stdComplexGaussian := by
  have h := (show MemLp (fun z : ℂ => z) ((a + b : ℕ) : ℝ≥0∞) stdComplexGaussian by
    simpa only [ENNReal.coe_natCast] using memLp_id_stdComplexGaussian ((a + b : ℕ) : ℝ≥0)).integrable_norm_pow'
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun z => by
    simp only [norm_mul, norm_pow, norm_star, pow_add]
    exact le_rfl

/-- The normalized complex Gaussian is centered (DH21 Lemma A.2, degree one). -/
theorem integral_id_stdComplexGaussian :
    ∫ z : ℂ, z ∂stdComplexGaussian = 0 := by
  rw [stdComplexGaussian, integral_map measurable_complexFromPair.aemeasurable
    (by fun_prop)]
  change (∫ x : ℝ × ℝ, Complex.equivRealProdCLM.symm x
    ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) = 0
  rw [ContinuousLinearEquiv.integral_comp_comm]
  have h := memLp_id_gaussianReal (μ := 0) (v := 1 / 2) 1
  have hf := (h.comp_fst (gaussianReal 0 (1 / 2))).integrable (by simp)
  have hs := (h.comp_snd (gaussianReal 0 (1 / 2))).integrable (by simp)
  simp only [id_eq] at hf hs
  have hp := integral_pair hf hs
  simp only [Prod.mk.eta] at hp
  rw [hp]
  rw [integral_prod _ hf, integral_prod _ hs]
  simp [integral_id_gaussianReal]

private theorem integral_sq_halfGaussian :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2) = 1 / 2 := by
  have h := variance_of_integral_eq_zero
    (μ := gaussianReal 0 (1 / 2)) measurable_id.aemeasurable
    (integral_id_gaussianReal (μ := 0) (v := 1 / 2))
  rw [variance_id_gaussianReal] at h
  simp only [id_eq] at h
  exact h.symm

/-- Unit second absolute moment, fixing the normalization in DH21 Lemma A.2. -/
theorem integral_norm_sq_stdComplexGaussian :
    ∫ z : ℂ, ‖z‖ ^ 2 ∂stdComplexGaussian = 1 := by
  rw [stdComplexGaussian, integral_map measurable_complexFromPair.aemeasurable (by fun_prop)]
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (1 / 2)) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1 / 2) 2).integrable_sq
  have hf := hi.comp_fst (gaussianReal 0 (1 / 2))
  have hs := hi.comp_snd (gaussianReal 0 (1 / 2))
  have he : (fun x : ℝ × ℝ => ‖Complex.equivRealProd.symm x‖ ^ 2) =
      fun x => x.1 ^ 2 + x.2 ^ 2 := by
    funext x
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.equivRealProd_symm_apply, pow_two]
  rw [he, integral_add hf hs, integral_prod _ hf, integral_prod _ hs]
  norm_num [integral_sq_halfGaussian]

private lemma charFunDual_halfGaussian (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 (1 / 2)) L = Complex.exp (- (L 1 : ℂ) ^ 2 / 4) := by
  rw [charFunDual_eq_charFun_map_one, gaussianReal_map_continuousLinearMap]
  simp only [charFun_gaussianReal, map_zero, Complex.ofReal_zero, Complex.ofReal_one,
    one_pow, mul_one]
  congr 1
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one,
    Real.coe_toNNReal', max_eq_left (sq_nonneg (L 1))]
  push_cast
  ring

/-- Characteristic function of the normalized complex Gaussian on the real dual. -/
theorem charFunDual_stdComplexGaussian (L : StrongDual ℝ ℂ) :
    charFunDual stdComplexGaussian L =
      Complex.exp (- ((L 1 : ℂ) ^ 2 + (L Complex.I : ℂ) ^ 2) / 4) := by
  rw [stdComplexGaussian]
  change charFunDual (((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
    Complex.equivRealProdCLM.symm.toContinuousLinearMap) L = _
  rw [charFunDual_map, charFunDual_prod, charFunDual_halfGaussian,
    charFunDual_halfGaussian, ← Complex.exp_add]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    Complex.equivRealProdCLM_symm_apply]
  norm_num
  ring
private lemma real_dual_complex (L : StrongDual ℝ ℂ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hz]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Multiplication by a complex number of norm one preserves the law (DH21 Lemma A.2). -/
theorem map_mul_stdComplexGaussian (c : ℂ) (hc : ‖c‖ = 1) :
    stdComplexGaussian.map (fun z => c * z) = stdComplexGaussian := by
  apply Measure.ext_of_charFunDual
  funext L
  change charFunDual (stdComplexGaussian.map (ContinuousLinearMap.mul ℝ ℂ c)) L = _
  rw [charFunDual_map, charFunDual_stdComplexGaussian, charFunDual_stdComplexGaussian]
  have hn : c.re ^ 2 + c.im ^ 2 = 1 := by
    calc
      _ = Complex.normSq c := by simp only [Complex.normSq_apply, pow_two]
      _ = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
      _ = 1 := by rw [hc]; norm_num
  have he : (L (c * 1)) ^ 2 + (L (c * Complex.I)) ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
    rw [real_dual_complex L (c * 1), real_dual_complex L (c * Complex.I)]
    simp only [mul_one, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    calc
      _ = (c.re ^ 2 + c.im ^ 2) * ((L 1) ^ 2 + (L Complex.I) ^ 2) := by ring
      _ = _ := by rw [hn, one_mul]
  congr 1
  simp only [ContinuousLinearMap.comp_apply]
  norm_cast
  change -(L (c * 1) ^ 2 + L (c * Complex.I) ^ 2) / 4 = _
  rw [he]

/-- Circular symmetry of the normalized complex Gaussian. -/
theorem map_rotation_stdComplexGaussian (θ : ℝ) :
    stdComplexGaussian.map (fun z => Complex.exp (θ * Complex.I) * z) =
      stdComplexGaussian := by
  apply map_mul_stdComplexGaussian
  simp

/-- Mixed moments of the centered normalized complex Gaussian (DH21 Lemma A.2).
In particular the covariance is one and all unbalanced moments vanish. -/
theorem integral_monomial_stdComplexGaussian (a b : ℕ) :
    (∫ z : ℂ, z ^ a * star z ^ b ∂stdComplexGaussian) =
      if a = b then (a.factorial : ℂ) else 0 := by
  rw [stdComplexGaussian, integral_map measurable_complexFromPair.aemeasurable (by fun_prop)]
  have h := ComplexGaussianPolynomial.expectation_mixed a b
  change (∫ x : ℝ × ℝ,
    MvPolynomial.eval (fun j : Fin 2 => if j = 0 then (x.1 : ℂ) else (x.2 : ℂ))
      (ComplexGaussianPolynomial.coordinate ^ a * ComplexGaussianPolynomial.conjugateCoordinate ^ b)
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) = _ at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [ComplexGaussianPolynomial.coordinate, ComplexGaussianPolynomial.conjugateCoordinate,
      Complex.equivRealProd_symm_apply, mul_comm, sub_eq_add_neg]

/-- DH21 Lemma A.2's scalar moment identity for a variable with the specified law. -/
theorem integral_monomial_of_hasLaw_stdComplexGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → ℂ} (hg : HasLaw g stdComplexGaussian P) (a b : ℕ) :
    (∫ ω, g ω ^ a * star (g ω) ^ b ∂P) =
      if a = b then (a.factorial : ℂ) else 0 := by
  have h := hg.integral_comp (f := fun z : ℂ => z ^ a * star z ^ b) (by fun_prop)
  exact h.trans (integral_monomial_stdComplexGaussian a b)

/-- Integrability of mixed monomials transfers along the complex Gaussian law. -/
theorem integrable_monomial_of_hasLaw_stdComplexGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → ℂ} (hg : HasLaw g stdComplexGaussian P) (a b : ℕ) :
    Integrable (fun ω => g ω ^ a * star (g ω) ^ b) P :=
  hg.integrable_comp (integrable_monomial_stdComplexGaussian a b)

/-- Rotation of any variable with the normalized complex Gaussian law preserves its law. -/
theorem hasLaw_rotation_stdComplexGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → ℂ} (hg : HasLaw g stdComplexGaussian P) (θ : ℝ) :
    HasLaw (fun ω => Complex.exp (θ * Complex.I) * g ω) stdComplexGaussian P := by
  have hr : HasLaw (fun z : ℂ => Complex.exp (θ * Complex.I) * z)
      stdComplexGaussian stdComplexGaussian :=
    ⟨by fun_prop, map_rotation_stdComplexGaussian θ⟩
  exact hr.comp hg

end WaveTurbulence

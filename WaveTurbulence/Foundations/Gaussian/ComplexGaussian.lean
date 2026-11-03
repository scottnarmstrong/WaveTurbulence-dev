/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
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

/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
@[expose] noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm

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

end WaveTurbulence

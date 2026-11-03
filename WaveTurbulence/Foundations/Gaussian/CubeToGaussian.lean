/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.BooleanCube
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# From the Boolean cube to the complex Gaussian vector

For a finite index type `ι` we approximate a vector of independent standard complex Gaussians
(law `Measure.pi fun _ : ι => stdComplexGaussian`) by normalized sums of independent uniform
signs,
`approxZ ι M x i = (2M)^{-1/2} ∑_{m < M} (s(x(i,T,m)) + i s(x(i,F,m)))`,
a function on the cube `ι × Bool × Fin M → Bool`.

## Main results

* `tendsto_approxLaw`: the laws of `approxZ ι M` converge weakly to the complex Gaussian law, by
  Lévy's continuity theorem (the characteristic functions are products of powers of
  `cos (u / √(2M))`, controlled by Mathlib's central limit lemma
  `tendsto_charFun_inv_sqrt_mul_pow`).
* `tendsto_favg_approxZ`: consequently, cube averages of `h ∘ approxZ ι M` converge to the
  Gaussian integral of `h`, for every bounded continuous `h`.
* `approxZ_mem_walshDeg`, `conj_approxZ_mem_walshDeg`, `favg_norm_sq_approxZ_le`: each coordinate
  of `approxZ ι M` (and its conjugate) has Walsh degree one and second moment at most one.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology BoundedContinuousFunction ENNReal

namespace WaveTurbulence.Gaussian

/-! ### Uniform measures on the cube -/

/-- The normalized complex Gaussian law is a probability measure. -/
instance isProbabilityMeasure_stdComplexGaussian_hc : IsProbabilityMeasure stdComplexGaussian := by
  unfold stdComplexGaussian
  infer_instance

/-- The uniform probability measure on `Bool`. -/
@[expose] noncomputable def boolMeasure : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

theorem boolMeasure_singleton (b : Bool) : boolMeasure {b} = 2⁻¹ := by
  cases b <;> simp [boolMeasure]

instance : IsProbabilityMeasure boolMeasure := by
  constructor
  simp only [boolMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem integral_boolMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Bool → E) : ∫ b, f b ∂boolMeasure = (2 : ℝ)⁻¹ • (f true + f false) := by
  rw [boolMeasure, integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite), integral_dirac, integral_dirac]
  simp

/-- The uniform probability measure on the cube `K → Bool`. -/
@[expose] noncomputable def cubeMeasure (K : Type*) [Fintype K] : Measure (K → Bool) :=
  Measure.pi fun _ => boolMeasure

instance (K : Type*) [Fintype K] : IsProbabilityMeasure (cubeMeasure K) := by
  unfold cubeMeasure
  infer_instance

/-- Integrals against the uniform cube measure are uniform averages. -/
theorem integral_cubeMeasure {K : Type*} [Fintype K] [DecidableEq K] (f : (K → Bool) → ℝ) :
    ∫ x, f x ∂cubeMeasure K = favg f := by
  rw [integral_fintype (Integrable.of_finite)]
  have hx : ∀ x : K → Bool, (cubeMeasure K).real {x} = ((Fintype.card (K → Bool) : ℝ))⁻¹ := by
    intro x
    simp only [Measure.real, cubeMeasure, Measure.pi_singleton, boolMeasure_singleton,
      prod_const, card_univ, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp
  simp only [hx, smul_eq_mul, favg, mul_sum]

/-- Integrals of product functions against the cube measure factorize. -/
theorem integral_cubeMeasure_prod {K : Type*} [Fintype K] (φ : K → Bool → ℂ) :
    ∫ x, ∏ k, φ k (x k) ∂cubeMeasure K = ∏ k, ∫ b, φ k b ∂boolMeasure :=
  integral_fintype_prod_eq_prod φ

/-! ### Characteristic functions of sign sums -/

theorem integral_bsign : ∫ b, bsign b ∂boolMeasure = 0 := by
  rw [integral_boolMeasure]
  simp [bsign]

theorem integral_bsign_sq : ∫ b, (bsign ^ 2) b ∂boolMeasure = 1 := by
  rw [integral_boolMeasure]
  norm_num [bsign]

/-- The characteristic function of a uniform random sign. -/
theorem integral_exp_bsign (v : ℝ) :
    ∫ b, Complex.exp (v * bsign b * Complex.I) ∂boolMeasure =
      charFun (boolMeasure.map bsign) v := by
  rw [charFun_apply_real, integral_map (measurable_of_finite _).aemeasurable
    (by fun_prop)]

theorem tendsto_charFun_bsign_pow (v : ℝ) :
    Tendsto (fun n : ℕ => charFun (boolMeasure.map bsign) ((√n)⁻¹ * v) ^ n) atTop
      (𝓝 (Complex.exp (-(v : ℂ) ^ 2 / 2))) :=
  tendsto_charFun_inv_sqrt_mul_pow (measurable_of_finite _).aemeasurable integral_bsign
    integral_bsign_sq v

/-- The characteristic function of a linear form in independent signs. -/
theorem integral_exp_sum_bsign {K : Type*} [Fintype K] (w : K → ℝ) :
    ∫ x, Complex.exp (((∑ k, w k * bsign (x k) : ℝ) : ℂ) * Complex.I) ∂cubeMeasure K =
      ∏ k, charFun (boolMeasure.map bsign) (w k) := by
  have h : ∀ x : K → Bool, Complex.exp (((∑ k, w k * bsign (x k) : ℝ) : ℂ) * Complex.I) =
      ∏ k, Complex.exp ((w k : ℂ) * bsign (x k) * Complex.I) := by
    intro x
    rw [Complex.ofReal_sum, sum_mul, Complex.exp_sum]
    push_cast
    rfl
  simp_rw [h]
  rw [integral_cubeMeasure_prod (fun k b => Complex.exp ((w k : ℂ) * bsign b * Complex.I))]
  simp_rw [integral_exp_bsign]

/-! ### The approximating vector -/

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The coefficients `(2M)^{-1/2}` (real direction) and `(2M)^{-1/2} i` (imaginary direction). -/
@[expose] noncomputable def approxCoeff (M : ℕ) (p : Bool × Fin M) : ℂ :=
  ((Real.sqrt (2 * M))⁻¹ : ℝ) * (if p.1 then 1 else Complex.I)

/-- The approximation of a vector of independent standard complex Gaussians indexed by `ι`,
built from `2M` independent signs per coordinate:
`Z_i = (2M)^{-1/2} ∑_{m < M} (s(x(i,T,m)) + i s(x(i,F,m)))`. -/
@[expose] noncomputable def approxZ (M : ℕ) (x : ι × Bool × Fin M → Bool) (i : ι) : ℂ :=
  ∑ p : Bool × Fin M, approxCoeff M p * (bsign (x (i, p)) : ℂ)

variable {ι}

omit [Fintype ι] [DecidableEq ι] in
theorem approxZ_mem_walshDeg (M : ℕ) (i : ι) :
    (fun x => approxZ ι M x i) ∈ walshDeg (ι × Bool × Fin M) 1 := by
  have h : (fun x => approxZ ι M x i) =
      ∑ p : Bool × Fin M, approxCoeff M p • fun x : ι × Bool × Fin M → Bool =>
        (bsign (x (i, p)) : ℂ) := by
    funext x
    simp [approxZ, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (bsign_mem_walshDeg _)

omit [Fintype ι] [DecidableEq ι] in
theorem conj_approxZ_mem_walshDeg (M : ℕ) (i : ι) :
    (fun x => (starRingEnd ℂ) (approxZ ι M x i)) ∈ walshDeg (ι × Bool × Fin M) 1 := by
  have h : (fun x => (starRingEnd ℂ) (approxZ ι M x i)) =
      ∑ p : Bool × Fin M, (starRingEnd ℂ) (approxCoeff M p) • fun x : ι × Bool × Fin M → Bool =>
        (bsign (x (i, p)) : ℂ) := by
    funext x
    simp [approxZ, Finset.sum_apply, map_sum, Complex.conj_ofReal]
  rw [h]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (bsign_mem_walshDeg _)

theorem favg_norm_sq_approxZ_le (M : ℕ) (i : ι) :
    favg (fun x => ‖approxZ ι M x i‖ ^ 2) ≤ 1 := by
  have h := favg_norm_sq_sum_bsign (K := ι × Bool × Fin M) (k := fun p : Bool × Fin M => (i, p))
    (fun a b hab => (Prod.mk.inj hab).2) (approxCoeff M)
  simp only [approxZ]
  rw [h]
  have hc : ∀ p : Bool × Fin M, ‖approxCoeff M p‖ ^ 2 = (2 * (M : ℝ))⁻¹ := by
    intro p
    have h1 : ‖(if p.1 then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
    rw [approxCoeff, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_pow, Real.sq_sqrt (by positivity)]
  simp only [hc, sum_const, card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  · have : (2 * (M : ℝ)) ≠ 0 := by positivity
    rw [mul_inv_cancel₀ this]

/-! ### Characteristic functions and weak convergence -/

omit [DecidableEq ι] in
/-- The real inner product with an approximating vector is a linear form in the signs. -/
theorem inner_toLp_approxZ (M : ℕ) (x : ι × Bool × Fin M → Bool)
    (t : PiLp 2 (fun _ : ι => ℂ)) :
    inner ℝ (WithLp.toLp 2 (approxZ ι M x)) t =
      ∑ k : ι × Bool × Fin M, inner ℝ (approxCoeff M k.2) (t k.1) * bsign (x k) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  simp only [approxZ, sum_inner]
  refine sum_congr rfl fun p _ => ?_
  rw [show approxCoeff M p * (bsign (x (i, p)) : ℂ) = bsign (x (i, p)) • approxCoeff M p by
    rw [Complex.real_smul, mul_comm], real_inner_smul_left, mul_comm]

theorem inner_approxCoeff (M : ℕ) (p : Bool × Fin M) (w : ℂ) :
    inner ℝ (approxCoeff M p) w = (Real.sqrt (2 * M))⁻¹ * (if p.1 then w.re else w.im) := by
  rw [approxCoeff]
  generalize (Real.sqrt (2 * M))⁻¹ = r
  rcases p with ⟨b, m⟩
  cases b <;> simp only [Complex.inner, ite_true, Bool.false_eq_true, ite_false, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_one, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.I_re, Complex.I_im, mul_neg, Complex.mul_im] <;>
    ring

/-- The law of the approximating vector, on `PiLp 2 (fun _ : ι => ℂ)`. -/
@[expose] noncomputable def approxLaw (M : ℕ) : Measure (PiLp 2 (fun _ : ι => ℂ)) :=
  (cubeMeasure (ι × Bool × Fin M)).map (fun x => WithLp.toLp 2 (approxZ ι M x))

/-- The law of a vector of independent standard complex Gaussians, on `PiLp 2`. -/
@[expose] noncomputable def gaussLaw : Measure (PiLp 2 (fun _ : ι => ℂ)) :=
  (Measure.pi fun _ : ι => stdComplexGaussian).map (WithLp.toLp 2)

instance (M : ℕ) : IsProbabilityMeasure (approxLaw (ι := ι) M) := by
  unfold approxLaw
  infer_instance

instance : IsProbabilityMeasure (gaussLaw (ι := ι)) := by
  unfold gaussLaw
  infer_instance

omit [DecidableEq ι] in
theorem charFun_approxLaw (M : ℕ) (t : PiLp 2 (fun _ : ι => ℂ)) :
    charFun (approxLaw M) t = ∏ i, (charFun (boolMeasure.map bsign)
      ((√(M : ℝ))⁻¹ * ((t i).re / √2)) ^ M *
      charFun (boolMeasure.map bsign) ((√(M : ℝ))⁻¹ * ((t i).im / √2)) ^ M) := by
  rw [charFun_apply, approxLaw, integral_map (measurable_of_finite _).aemeasurable
    (by fun_prop)]
  simp_rw [inner_toLp_approxZ, inner_approxCoeff]
  have h := integral_exp_sum_bsign (K := ι × Bool × Fin M)
    (fun k => (Real.sqrt (2 * M))⁻¹ * (if k.2.1 then (t k.1).re else (t k.1).im))
  rw [h, Fintype.prod_prod_type]
  refine prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false, prod_const, card_univ, Fintype.card_fin]
  have hs : (Real.sqrt (2 * M))⁻¹ = (√(M : ℝ))⁻¹ * (√2)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv, mul_comm]
  rw [hs]
  congr 3 <;> ring

theorem charFun_stdComplexGaussian (w : ℂ) :
    charFun stdComplexGaussian w =
      Complex.exp (-((w.re / √2 : ℝ) : ℂ) ^ 2 / 2) *
        Complex.exp (-((w.im / √2 : ℝ) : ℂ) ^ 2 / 2) := by
  have hmeas : Measurable Complex.equivRealProd.symm :=
    Complex.equivRealProdCLM.symm.continuous.measurable
  rw [charFun_apply, stdComplexGaussian, integral_map hmeas.aemeasurable (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, Complex.exp (((inner ℝ (Complex.equivRealProd.symm p) w : ℝ) : ℂ) *
      Complex.I) = Complex.exp ((w.re : ℂ) * p.1 * Complex.I) *
        Complex.exp ((w.im : ℂ) * p.2 * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.inner, Complex.equivRealProd_symm_apply, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
      Complex.neg_re, Complex.neg_im]
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp ((w.re : ℂ) * x * Complex.I))
    (fun y : ℝ => Complex.exp ((w.im : ℂ) * y * Complex.I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal]
  congr 1 <;> congr 1 <;> push_cast <;>
    rw [div_pow, ← Complex.ofReal_pow (√2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
    push_cast <;> ring

omit [DecidableEq ι] in
theorem charFun_gaussLaw (t : PiLp 2 (fun _ : ι => ℂ)) :
    charFun (gaussLaw (ι := ι)) t = ∏ i, (Complex.exp (-(((t i).re / √2 : ℝ) : ℂ) ^ 2 / 2) *
      Complex.exp (-(((t i).im / √2 : ℝ) : ℂ) ^ 2 / 2)) := by
  rw [gaussLaw, charFun_pi]
  simp_rw [charFun_stdComplexGaussian]

/-- The law of the approximating vector, as a probability measure. -/
@[expose] noncomputable def approxPM (M : ℕ) : ProbabilityMeasure (PiLp 2 (fun _ : ι => ℂ)) :=
  ⟨approxLaw M, inferInstance⟩

/-- The complex Gaussian law, as a probability measure. -/
@[expose] noncomputable def gaussPM : ProbabilityMeasure (PiLp 2 (fun _ : ι => ℂ)) :=
  ⟨gaussLaw, inferInstance⟩

omit [DecidableEq ι] in
/-- **Central limit theorem for the approximation**: the laws of `approxZ ι M` converge weakly to
the law of a vector of independent standard complex Gaussians. -/
theorem tendsto_approxPM :
    Tendsto (fun M : ℕ => approxPM (ι := ι) M) atTop (𝓝 (gaussPM (ι := ι))) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  simp only [approxPM, gaussPM, ProbabilityMeasure.coe_mk]
  simp_rw [charFun_approxLaw, charFun_gaussLaw]
  refine tendsto_finsetProd _ fun i _ => ?_
  exact (tendsto_charFun_bsign_pow _).mul (tendsto_charFun_bsign_pow _)

/-- Cube averages of bounded continuous functions of the approximating vector converge to the
Gaussian integral. -/
theorem tendsto_favg_approxZ {h : (ι → ℂ) → ℝ} (hcont : Continuous h) {C : ℝ}
    (hC : ∀ z, |h z| ≤ C) :
    Tendsto (fun M : ℕ => favg (fun x => h (approxZ ι M x))) atTop
      (𝓝 (∫ z, h z ∂Measure.pi fun _ : ι => stdComplexGaussian)) := by
  have hcF : Continuous fun v : PiLp 2 (fun _ : ι => ℂ) => h (WithLp.ofLp v) :=
    hcont.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : ι => ℂ))
  let F : PiLp 2 (fun _ : ι => ℂ) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun v => h (WithLp.ofLp v)) hcF C
      (fun v => by rw [Real.norm_eq_abs]; exact hC _)
  have hT := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_approxPM) F
  simp only [approxPM, gaussPM, ProbabilityMeasure.coe_mk] at hT
  have hlhs : ∀ M : ℕ, ∫ v, F v ∂(approxLaw (ι := ι) M) = favg (fun x => h (approxZ ι M x)) := by
    intro M
    rw [approxLaw, integral_map (measurable_of_finite _).aemeasurable
      F.continuous.aestronglyMeasurable, integral_cubeMeasure]
    rfl
  have hrhs : ∫ v, F v ∂(gaussLaw (ι := ι)) =
      ∫ z, h z ∂Measure.pi fun _ : ι => stdComplexGaussian := by
    rw [gaussLaw, integral_map (WithLp.measurable_toLp 2 (ι → ℂ)).aemeasurable
      F.continuous.aestronglyMeasurable]
    rfl
  simpa only [hlhs, hrhs] using hT

end WaveTurbulence.Gaussian

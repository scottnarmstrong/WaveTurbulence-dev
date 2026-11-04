/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.OfAny
public import WaveTurbulence.Foundations.ClassJR.CouplingS

/-!
# The time integral `∫_0^t e^{πixu} du` as a superposition of exponentials

DH21 §5.5 (proof of Proposition 5.1, (regcplexpl)–(regcplex2), L1104–L1108, and (expandG)–(propertyG),
L1121–L1124) writes the time integrals `∫_0^t e^{πixu} du`, `t ∈ [0, 1]`, as superpositions
`∫ G(λ) e^{πiλt} dλ` by inserting the cutoffs `χ₀(x)` and `χ_∞(x)`:
* the `χ₀` part is `∫∫ kerM(x; σ, τ) e^{πiσt} dσ dτ` (`integral_kerM_mul_exp`);
* the `χ_∞` part is `Φ(x) (e^{πixt} - 1)`, and DH21 (extraid) writes `e^{πixt} = ∫ M₀(λ - x) e^{πiλt} dλ`
  and `1 = ∫ M₀(λ) e^{πiλt} dλ`.

Hence `eInt x t = ∫ gE x q e^{πi q.1 t} dq` for `t ∈ [0, 1]` (`integral_gE_mul_exp`), with
`gE x (λ, τ) = kerM x (λ, τ) + 1_{[0,1]}(τ) Φ(x) (M₀(λ - x) - M₀(λ))`.

The variable `τ` of `kerM` is kept, as in `KernelM.lean`. This file also proves the Gevrey derivative
bounds of `gE`:
* in `x` (`norm_iteratedDeriv_gE_le`), used in Case 1 of Proposition 5.1;
* along the diagonal `u ↦ gE (c - u) (λ - u, τ)` (`norm_iteratedDeriv_gED_le`), used in Lemma G (DH21
  (expandG)), where the bundle `ℓ(α) = u` shifts both arguments.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Constants

/-- The decay constants of the derivatives of `M₀ = ftπ ψ₀`. -/
theorem exists_M0_deriv_bound : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
    ∀ n σ, ‖iteratedDeriv n M0 σ‖ ≤ K * B ^ n / (1 + |σ|) ^ 3 :=
  exists_norm_iteratedDeriv_ftπ_le contDiff_psi0 hasCompactSupport_psi0

/-- The constant of the derivatives of `M₀`. -/
@[expose] noncomputable def KM0 : ℝ := exists_M0_deriv_bound.choose

/-- The radius of the derivatives of `M₀`. -/
@[expose] noncomputable def BM0 : ℝ := exists_M0_deriv_bound.choose_spec.choose

theorem M0_deriv_bound : 0 ≤ KM0 ∧ 0 ≤ BM0 ∧
    ∀ n σ, ‖iteratedDeriv n M0 σ‖ ≤ KM0 * BM0 ^ n / (1 + |σ|) ^ 3 :=
  exists_M0_deriv_bound.choose_spec.choose_spec

/-- The decay constants of the derivatives of `ftπ φ` (the profile of `kerM`). -/
theorem exists_FP_deriv_bound : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
    ∀ n σ, ‖iteratedDeriv n (ftπ phiM) σ‖ ≤ K * B ^ n / (1 + |σ|) ^ 3 :=
  exists_norm_iteratedDeriv_ftπ_le contDiff_phiM hasCompactSupport_phiM

/-- The constant of the derivatives of `ftπ φ`. -/
@[expose] noncomputable def KFP : ℝ := exists_FP_deriv_bound.choose

/-- The radius of the derivatives of `ftπ φ`. -/
@[expose] noncomputable def BFP : ℝ := exists_FP_deriv_bound.choose_spec.choose

theorem FP_deriv_bound : 0 ≤ KFP ∧ 0 ≤ BFP ∧
    ∀ n σ, ‖iteratedDeriv n (ftπ phiM) σ‖ ≤ KFP * BFP ^ n / (1 + |σ|) ^ 3 :=
  exists_FP_deriv_bound.choose_spec.choose_spec

/-- The Gevrey radius of the main-coefficient calculus: it dominates `A0` and the radii of `M₀`
and `ftπ φ`. -/
@[expose] noncomputable def A1 : ℝ := max A0 (max BM0 BFP)

theorem A0_le_A1 : A0 ≤ A1 := le_max_left _ _
theorem BM0_le_A1 : BM0 ≤ A1 := (le_max_left _ _).trans (le_max_right _ _)
theorem BFP_le_A1 : BFP ≤ A1 := (le_max_right _ _).trans (le_max_right _ _)
theorem A1_nonneg : 0 ≤ A1 := A0_nonneg.trans A0_le_A1
theorem Achi_le_A1 : Achi ≤ A1 := Achi_le_A0.trans A0_le_A1
theorem AkM_le_A1 : AkM ≤ A1 := AkM_le_A0.trans A0_le_A1

end Constants

section Gevrey

/-- **The Gevrey Leibniz rule in one variable**: if `|∂^i f| ≤ a A^i (2i)!` and
`|∂^i g| ≤ b A^i (2i)!` then `|∂^k (fg)| ≤ 4ab A^k (2k)!` (DH21 Lemma A.4 with two factors). -/
theorem norm_iteratedDeriv_mul_gevrey {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {x a b A : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hfx : ∀ i, ‖iteratedDeriv i f x‖ ≤ a * A ^ i * (Nat.factorial (2 * i) : ℝ))
    (hgx : ∀ i, ‖iteratedDeriv i g x‖ ≤ b * A ^ i * (Nat.factorial (2 * i) : ℝ)) (k : ℕ) :
    ‖iteratedDeriv k (fun y => f y * g y) x‖ ≤ 4 * a * b * A ^ k * (Nat.factorial (2 * k) : ℝ) := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast le_top)).trans ?_
  simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  calc ∑ i ∈ range (k + 1), (k.choose i : ℝ) * ‖iteratedDeriv i f x‖ *
        ‖iteratedDeriv (k - i) g x‖
      ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (a * A ^ i * (Nat.factorial (2 * i) : ℝ)) *
          (b * A ^ (k - i) * (Nat.factorial (2 * (k - i)) : ℝ)) := by
        gcongr with i hi
        · exact hfx i
        · exact hgx (k - i)
    _ = a * b * A ^ k * ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (Nat.factorial (2 * i) : ℝ) *
          (Nat.factorial (2 * (k - i)) : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have : A ^ k = A ^ i * A ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hik]
        rw [this]
        ring
    _ ≤ a * b * A ^ k * (4 * (Nat.factorial (2 * k) : ℝ)) :=
        mul_le_mul_of_nonneg_left (Combinatorics.sum_choose_factorial_le k) (by positivity)
    _ = _ := by ring

/-- A geometric bound is a Gevrey bound. -/
theorem geom_le_gevrey {K B A : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hBA : B ≤ A) (i : ℕ) :
    K * B ^ i ≤ K * A ^ i * (Nat.factorial (2 * i) : ℝ) := by
  have h1 : (1 : ℝ) ≤ (Nat.factorial (2 * i) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc K * B ^ i ≤ K * A ^ i := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBA i) hK
    _ ≤ K * A ^ i * (Nat.factorial (2 * i) : ℝ) :=
        le_mul_of_one_le_right (mul_nonneg hK (pow_nonneg (hB.trans hBA) i)) h1

end Gevrey

section Rep

/-- The indicator `1_{[0,1]}` with complex values. -/
@[expose] noncomputable def ind01 (τ : ℝ) : ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) τ

theorem measurable_ind01 : Measurable ind01 :=
  measurable_const.indicator measurableSet_Icc

theorem norm_ind01_le (τ : ℝ) : ‖ind01 τ‖ ≤ 1 := by
  unfold ind01
  by_cases h : τ ∈ Icc (0 : ℝ) 1
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

theorem integral_ind01 : ∫ τ, ind01 τ = 1 := by
  unfold ind01
  rw [integral_indicator_const _ measurableSet_Icc]
  simp

theorem integrable_ind01 : Integrable ind01 := by
  unfold ind01
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

/-- **The coefficient of `∫_0^t e^{πixu} du`**:
`gE x (λ, τ) = kerM x (λ, τ) + 1_{[0,1]}(τ) Φ(x) (M₀(λ - x) - M₀(λ))`. -/
@[expose] noncomputable def gE (x : ℝ) (q : ℝ × ℝ) : ℂ :=
  kerM x q + ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1))

theorem continuous_phiR : Continuous phiR := contDiff_phiR.continuous

theorem measurable_gE : Measurable (Function.uncurry gE) := by
  unfold gE
  refine measurable_kerM.add ?_
  refine (measurable_ind01.comp (measurable_snd.comp measurable_snd)).mul ?_
  refine (continuous_phiR.measurable.comp measurable_fst).mul ?_
  exact (continuous_M0.measurable.comp ((measurable_fst.comp measurable_snd).sub measurable_fst)).sub
    (continuous_M0.measurable.comp (measurable_fst.comp measurable_snd))

/-- `∫ M₀(λ - x) e^{πiλt} dλ = e^{πixt}` for `t ∈ [0, 1]` (DH21 (extraid)). -/
theorem integral_M0_shift_mul_exp (x : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ v, M0 (v - x) * cexp (π * I * (v * t)) = cexp (π * I * (x * t)) := by
  rw [extraid x ht]
  have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun v => M0 (v - x) * cexp (π * I * (v * t))) (-x)
  simp only [sub_neg_eq_add, add_sub_cancel_right] at this
  rw [← this]
  congr 1
  funext σ
  congr 3
  push_cast
  ring

theorem integrable_M0_shift_mul_exp (x t : ℝ) :
    Integrable fun v => M0 (v - x) * cexp (π * I * (v * t)) := by
  refine ((integrable_M0.comp_sub_right x).mul_bdd (c := 1) ?_ ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => cexp (π * I * (v * t))).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [Complex.norm_exp]
    simp

/-- **The time integral as a superposition of exponentials**: for `t ∈ [0, 1]`,
`∫_0^t e^{πixu} du = ∫ gE x q e^{πi q.1 t} dq`. -/
theorem integral_gE_mul_exp (x : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ q : ℝ × ℝ, gE x q * cexp (π * I * (q.1 * t)) = eInt x t := by
  have hcont : Continuous fun q : ℝ × ℝ => cexp (π * I * (q.1 * t)) := by fun_prop
  have h1 : Integrable fun q : ℝ × ℝ => kerM x q * cexp (π * I * (q.1 * t)) :=
    integrable_kerM_mul x hcont.aestronglyMeasurable (fun q => by rw [Complex.norm_exp]; simp)
  have hF : Integrable fun v : ℝ => phiR x * (M0 (v - x) - M0 v) * cexp (π * I * (v * t)) := by
    have : (fun v : ℝ => phiR x * (M0 (v - x) - M0 v) * cexp (π * I * (v * t))) = fun v =>
        phiR x * (M0 (v - x) * cexp (π * I * (v * t)) - M0 v * cexp (π * I * (v * t))) := by
      funext v; ring
    rw [this]
    refine Integrable.const_mul ((integrable_M0_shift_mul_exp x t).sub ?_) _
    simpa using integrable_M0_shift_mul_exp 0 t
  have h2 : Integrable fun q : ℝ × ℝ =>
      ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1)) * cexp (π * I * (q.1 * t)) := by
    have : (fun q : ℝ × ℝ => ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1)) *
        cexp (π * I * (q.1 * t))) = fun q =>
        (phiR x * (M0 (q.1 - x) - M0 q.1) * cexp (π * I * (q.1 * t))) * ind01 q.2 := by
      funext q; ring
    rw [this, Measure.volume_eq_prod]
    exact hF.mul_prod integrable_ind01
  have e : (fun q : ℝ × ℝ => gE x q * cexp (π * I * (q.1 * t))) = fun q =>
      kerM x q * cexp (π * I * (q.1 * t)) +
        ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1)) * cexp (π * I * (q.1 * t)) := by
    funext q; unfold gE; ring
  rw [e, integral_add h1 h2, integral_kerM_mul_exp x ht]
  have h3 : ∫ q : ℝ × ℝ, ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1)) *
      cexp (π * I * (q.1 * t)) = phiR x * (cexp (π * I * (x * t)) - 1) := by
    have : (fun q : ℝ × ℝ => ind01 q.2 * (phiR x * (M0 (q.1 - x) - M0 q.1)) *
        cexp (π * I * (q.1 * t))) = fun q =>
        (phiR x * (M0 (q.1 - x) - M0 q.1) * cexp (π * I * (q.1 * t))) * ind01 q.2 := by
      funext q; ring
    rw [this, Measure.volume_eq_prod, integral_prod_mul
      (f := fun v : ℝ => phiR x * (M0 (v - x) - M0 v) * cexp (π * I * (v * t))) (g := ind01),
      integral_ind01, mul_one]
    have : (fun v : ℝ => phiR x * (M0 (v - x) - M0 v) * cexp (π * I * (v * t))) = fun v =>
        phiR x * (M0 (v - x) * cexp (π * I * (v * t)) - M0 v * cexp (π * I * (v * t))) := by
      funext v; ring
    rw [this, integral_const_mul, integral_sub (integrable_M0_shift_mul_exp x t)
      (by simpa using integrable_M0_shift_mul_exp 0 t), integral_M0_shift_mul_exp x ht]
    have h0 := integral_M0_shift_mul_exp 0 ht
    simp only [sub_zero, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero] at h0
    rw [h0]
  rw [h3, ← chiInfinity_mul_eInt, ← add_mul]
  rw [show (chi0 x : ℂ) + (chiInfinity x : ℂ) = 1 by
    rw [chiInfinity]; push_cast; ring, one_mul]

end Rep

section Pointwise

/-- The real indicator `1_{[0,1]}`. -/
@[expose] noncomputable def ind01r (τ : ℝ) : ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) τ

theorem ind01r_nonneg (τ : ℝ) : 0 ≤ ind01r τ := by
  unfold ind01r; by_cases h : τ ∈ Icc (0 : ℝ) 1 <;> simp [h]

theorem norm_ind01 (τ : ℝ) : ‖ind01 τ‖ = ind01r τ := by
  unfold ind01 ind01r; by_cases h : τ ∈ Icc (0 : ℝ) 1 <;> simp [h]

/-- The constant of the derivative bounds of `gE`. -/
@[expose] noncomputable def CE : ℝ := 8 * Real.exp 4 * KFP + 2 * CkM + 5 * CPhi * KM0

theorem CE_nonneg : 0 ≤ CE := by
  have := M0_deriv_bound.1; have := FP_deriv_bound.1; have := kerM_bound.1; have := CPhi_nonneg
  unfold CE; positivity

theorem contDiff_M0 : ContDiff ℝ ∞ M0 := contDiff_ftπ contDiff_psi0 hasCompactSupport_psi0

/-- A smooth function is `C^j` at every point. -/
theorem ContDiff.cdAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (h : ContDiff ℝ ∞ f) (j : ℕ) (x : E) : ContDiffAt ℝ j f x :=
  (h.of_le (by exact_mod_cast le_top)).contDiffAt

theorem contDiff_gE (q : ℝ × ℝ) : ContDiff ℝ ∞ fun y => gE y q := by
  unfold gE
  exact (contDiff_kerM q).add (contDiff_const.mul (contDiff_phiR.mul
    ((contDiff_M0.comp (contDiff_const.sub contDiff_id)).sub contDiff_const)))

/-- `|∂^i Φ(x)| ≤ C_Φ A₁^i (2i)! / (1 + |x|)`. -/
theorem norm_iteratedDeriv_phiR_le_decay (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i phiR x‖ ≤ CPhi / (1 + |x|) * A1 ^ i * (Nat.factorial (2 * i) : ℝ) := by
  have hp : 0 < 1 + |x| := by positivity
  have h := phiR_gevrey i x
  have hA : Achi ^ i ≤ A1 ^ i := pow_le_pow_left₀ Achi_nonneg Achi_le_A1 i
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hp]
  calc ‖iteratedDeriv i phiR x‖ * (1 + |x|) = (1 + |x|) * ‖iteratedDeriv i phiR x‖ := mul_comm _ _
    _ ≤ CPhi * Achi ^ i * (Nat.factorial (2 * i) : ℝ) := h
    _ ≤ CPhi * A1 ^ i * (Nat.factorial (2 * i) : ℝ) := by
        have := CPhi_nonneg; gcongr

/-- `|∂^i M₀(σ)| ≤ K A₁^i (2i)! / (1 + |σ|)^3`. -/
theorem norm_iteratedDeriv_M0_le (i : ℕ) (σ : ℝ) :
    ‖iteratedDeriv i M0 σ‖ ≤ KM0 / (1 + |σ|) ^ 3 * A1 ^ i * (Nat.factorial (2 * i) : ℝ) := by
  obtain ⟨hK, hB, h⟩ := M0_deriv_bound
  have hp : 0 < (1 + |σ|) ^ 3 := by positivity
  calc ‖iteratedDeriv i M0 σ‖ ≤ KM0 * BM0 ^ i / (1 + |σ|) ^ 3 := h i σ
    _ = (KM0 / (1 + |σ|) ^ 3) * BM0 ^ i := by ring
    _ ≤ (KM0 / (1 + |σ|) ^ 3) * A1 ^ i * (Nat.factorial (2 * i) : ℝ) :=
        geom_le_gevrey (by positivity) hB BM0_le_A1 i

/-- Derivatives of `y ↦ f(σ - y)`. -/
theorem norm_iteratedDeriv_sub_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (σ x : ℝ) (m : ℕ) :
    ‖iteratedDeriv m (fun y => f (σ - y)) x‖ ≤ ‖iteratedDeriv m f (σ - x)‖ := by
  have h := norm_iteratedDeriv_comp_affine_le hf (τ := 1) (by norm_num) σ x m
  simpa using h

/-- **Pointwise derivative bounds of `gE` in `x`.** -/
theorem norm_iteratedDeriv_gE_le (j : ℕ) (x : ℝ) (q : ℝ × ℝ) :
    ‖iteratedDeriv j (fun y => gE y q) x‖ ≤
      CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |x|) *
        (1 / (1 + |q.1|) ^ 3 + 1 / (1 + |q.1 - x|) ^ 3) := by
  have hp : 0 < 1 + |x| := by positivity
  have hq1 : 0 < (1 + |q.1|) ^ 3 := by positivity
  have hq2 : 0 < (1 + |q.1 - x|) ^ 3 := by positivity
  have hG : (0 : ℝ) ≤ A1 ^ j * (Nat.factorial (2 * j) : ℝ) := by have := A1_nonneg; positivity
  have hind := ind01r_nonneg q.2
  obtain ⟨hCk, hAk, hk⟩ := kerM_bound
  have hKM := M0_deriv_bound.1
  have hCP := CPhi_nonneg
  -- the pieces
  have hM : ContDiff ℝ ∞ fun y => M0 (q.1 - y) := contDiff_M0.comp (contDiff_const.sub contDiff_id)
  have hP : ContDiff ℝ ∞ fun y => phiR y * (M0 (q.1 - y) - M0 q.1) :=
    contDiff_phiR.mul (hM.sub contDiff_const)
  have e : iteratedDeriv j (fun y => gE y q) x = iteratedDeriv j (fun y => kerM y q) x +
      ind01 q.2 * (iteratedDeriv j (fun y => phiR y * M0 (q.1 - y)) x -
        M0 q.1 * iteratedDeriv j phiR x) := by
    have h1 : (fun y => gE y q) = fun y => kerM y q +
        ind01 q.2 * (phiR y * M0 (q.1 - y) - M0 q.1 * phiR y) := by
      funext y; unfold gE; ring
    have hD : ContDiff ℝ ∞ fun y => phiR y * M0 (q.1 - y) - M0 q.1 * phiR y :=
      (contDiff_phiR.mul hM).sub (contDiff_const.mul contDiff_phiR)
    rw [h1, iteratedDeriv_fun_add (ContDiff.cdAt (contDiff_kerM q) j x)
        (ContDiff.cdAt (contDiff_const.mul hD) j x),
      iteratedDeriv_const_mul _ (ContDiff.cdAt hD j x),
      iteratedDeriv_fun_sub (ContDiff.cdAt (contDiff_phiR.mul hM) j x)
        (ContDiff.cdAt (contDiff_const.mul contDiff_phiR) j x),
      iteratedDeriv_const_mul _ (ContDiff.cdAt contDiff_phiR j x)]
  rw [e]
  -- the χ₀ part
  have hker : ‖iteratedDeriv j (fun y => kerM y q) x‖ ≤
      2 * CkM * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |x|) *
        (1 / (1 + |q.1|) ^ 3) := by
    by_cases hx : 1 < |x|
    · rw [iteratedDeriv_kerM_eq_zero hx, norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        hCk) (pow_nonneg A1_nonneg _)) (by positivity)) hind) hp.le) (by positivity)
    · push Not at hx
      have h2 : 1 ≤ 2 / (1 + |x|) := by rw [le_div_iff₀ hp]; linarith
      have hA : AkM ^ j ≤ A1 ^ j := pow_le_pow_left₀ hAk AkM_le_A1 j
      calc ‖iteratedDeriv j (fun y => kerM y q) x‖
          ≤ ind01r q.2 * (CkM * AkM ^ j * (Nat.factorial (2 * j) : ℝ)) / (1 + |q.1|) ^ 3 :=
            hk j x q
        _ ≤ ind01r q.2 * (CkM * A1 ^ j * (Nat.factorial (2 * j) : ℝ)) / (1 + |q.1|) ^ 3 := by
            gcongr
        _ = 1 * (CkM * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 * (1 / (1 + |q.1|) ^ 3)) := by
            ring
        _ ≤ (2 / (1 + |x|)) * (CkM * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 *
              (1 / (1 + |q.1|) ^ 3)) := by
            refine mul_le_mul_of_nonneg_right h2 ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCk (pow_nonneg A1_nonneg _))
              (by positivity)) hind) (by positivity)
        _ = _ := by ring
  -- the `Φ M₀(q.1 - x)` part
  have hpm : ‖iteratedDeriv j (fun y => phiR y * M0 (q.1 - y)) x‖ ≤
      4 * (CPhi / (1 + |x|)) * (KM0 / (1 + |q.1 - x|) ^ 3) * A1 ^ j *
        (Nat.factorial (2 * j) : ℝ) :=
    norm_iteratedDeriv_mul_gevrey contDiff_phiR hM (by positivity) (by positivity) A1_nonneg
      (fun i => norm_iteratedDeriv_phiR_le_decay i x)
      (fun i => (norm_iteratedDeriv_sub_le contDiff_M0 q.1 x i).trans
        (norm_iteratedDeriv_M0_le i (q.1 - x))) j
  -- the `Φ M₀(q.1)` part
  have hm0 : ‖M0 q.1 * iteratedDeriv j phiR x‖ ≤
      KM0 / (1 + |q.1|) ^ 3 * (CPhi / (1 + |x|) * A1 ^ j * (Nat.factorial (2 * j) : ℝ)) := by
    rw [norm_mul]
    refine mul_le_mul ?_ (norm_iteratedDeriv_phiR_le_decay j x) (norm_nonneg _) (by positivity)
    simpa using norm_iteratedDeriv_M0_le 0 q.1
  calc ‖iteratedDeriv j (fun y => kerM y q) x + ind01 q.2 *
        (iteratedDeriv j (fun y => phiR y * M0 (q.1 - y)) x - M0 q.1 * iteratedDeriv j phiR x)‖
      ≤ ‖iteratedDeriv j (fun y => kerM y q) x‖ + ind01r q.2 *
          (‖iteratedDeriv j (fun y => phiR y * M0 (q.1 - y)) x‖ +
            ‖M0 q.1 * iteratedDeriv j phiR x‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_ind01]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hind
    _ ≤ 2 * CkM * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |x|) *
          (1 / (1 + |q.1|) ^ 3) + ind01r q.2 *
          (4 * (CPhi / (1 + |x|)) * (KM0 / (1 + |q.1 - x|) ^ 3) * A1 ^ j *
            (Nat.factorial (2 * j) : ℝ) +
          KM0 / (1 + |q.1|) ^ 3 * (CPhi / (1 + |x|) * A1 ^ j * (Nat.factorial (2 * j) : ℝ))) := by
        gcongr
    _ = A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |x|) *
          ((2 * CkM + CPhi * KM0) * (1 / (1 + |q.1|) ^ 3) +
            4 * CPhi * KM0 * (1 / (1 + |q.1 - x|) ^ 3)) := by
        field_simp
        ring
    _ ≤ A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |x|) *
          (CE * (1 / (1 + |q.1|) ^ 3) + CE * (1 / (1 + |q.1 - x|) ^ 3)) := by
        have h1 : 2 * CkM + CPhi * KM0 ≤ CE := by
          have := FP_deriv_bound.1
          have : 0 ≤ Real.exp 4 * KFP := by positivity
          have : 0 ≤ CPhi * KM0 := by positivity
          unfold CE; nlinarith
        have h2 : 4 * CPhi * KM0 ≤ CE := by
          have := FP_deriv_bound.1
          have : 0 ≤ Real.exp 4 * KFP := by positivity
          have : 0 ≤ CPhi * KM0 := by positivity
          unfold CE; nlinarith
        gcongr
    _ = _ := by ring

end Pointwise

section Diagonal

theorem contDiff_chi0c : ContDiff ℝ ∞ fun y => (chi0 y : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (chi0_contDiff (n := ⊤))

theorem contDiff_FP : ContDiff ℝ ∞ (ftπ phiM) := contDiff_ftπ contDiff_phiM hasCompactSupport_phiM

/-- The diagonal family `u ↦ gE (c - u) (v - u, τ)` on `τ ∈ [0, 1]`. -/
theorem gE_diag_eq {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (c v : ℝ) :
    (fun y => gE (c - y) (v - y, τ)) = fun y =>
      (chi0 (c - y) : ℂ) * ftπ phiM (v - τ * c - (1 - τ) * y) +
        (phiR (c - y) * M0 (v - c) - phiR (c - y) * M0 (v - y)) := by
  funext y
  simp only [gE, kerM, ind01, Set.indicator_of_mem hτ, mul_one, one_mul]
  congr 1
  · rw [show v - y - τ * (c - y) = v - τ * c - (1 - τ) * y by ring]
  · ring_nf

theorem gE_diag_eq_zero {τ : ℝ} (hτ : τ ∉ Icc (0 : ℝ) 1) (c v : ℝ) :
    (fun y => gE (c - y) (v - y, τ)) = fun _ => 0 := by
  funext y
  simp [gE, kerM, ind01, Set.indicator_of_notMem hτ]

/-- **Pointwise derivative bounds of `gE` along the diagonal.** -/
theorem norm_iteratedDeriv_gED_le (j : ℕ) (c u v τ : ℝ) :
    ‖iteratedDeriv j (fun y => gE (c - y) (v - y, τ)) u‖ ≤
      CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r τ / (1 + |c - u|) *
        (1 / (1 + |v - u - τ * (c - u)|) ^ 3 + 1 / (1 + |v - c|) ^ 3 + 1 / (1 + |v - u|) ^ 3) := by
  have hp : 0 < 1 + |c - u| := by positivity
  have hKM := M0_deriv_bound.1
  have hKF := FP_deriv_bound.1
  have hCP := CPhi_nonneg
  by_cases hτ : τ ∈ Icc (0 : ℝ) 1
  swap
  · rw [gE_diag_eq_zero hτ, iteratedDeriv_const]
    have : ind01r τ = 0 := by simp [ind01r, Set.indicator_of_notMem hτ]
    rw [this]
    split_ifs <;> simp
  have hind : ind01r τ = 1 := by simp [ind01r, Set.indicator_of_mem hτ]
  rw [hind, gE_diag_eq hτ]
  have hτ1 : |1 - τ| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
  have hC : ContDiff ℝ ∞ fun y => (chi0 (c - y) : ℂ) :=
    contDiff_chi0c.comp (contDiff_const.sub contDiff_id)
  have hF : ContDiff ℝ ∞ fun y => ftπ phiM (v - τ * c - (1 - τ) * y) :=
    contDiff_FP.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  have hP : ContDiff ℝ ∞ fun y => phiR (c - y) := contDiff_phiR.comp (contDiff_const.sub contDiff_id)
  have hM : ContDiff ℝ ∞ fun y => M0 (v - y) := contDiff_M0.comp (contDiff_const.sub contDiff_id)
  have hPd : ∀ i, ‖iteratedDeriv i (fun y => phiR (c - y)) u‖ ≤
      CPhi / (1 + |c - u|) * A1 ^ i * (Nat.factorial (2 * i) : ℝ) := fun i =>
    (norm_iteratedDeriv_sub_le contDiff_phiR c u i).trans (norm_iteratedDeriv_phiR_le_decay i _)
  rw [iteratedDeriv_fun_add (ContDiff.cdAt (hC.mul hF) j u)
      (ContDiff.cdAt ((hP.mul contDiff_const).sub (hP.mul hM)) j u),
    iteratedDeriv_fun_sub (ContDiff.cdAt (hP.mul contDiff_const) j u)
      (ContDiff.cdAt (hP.mul hM) j u)]
  -- the `χ₀` part
  have hker : ‖iteratedDeriv j (fun y => (chi0 (c - y) : ℂ) * ftπ phiM (v - τ * c - (1 - τ) * y))
      u‖ ≤ 8 * Real.exp 4 * KFP / (1 + |c - u|) * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) *
        A1 ^ j * (Nat.factorial (2 * j) : ℝ) := by
    by_cases hcu : 1 < |c - u|
    · rw [iteratedDeriv_eq_zero_of_eventuallyEq_zero (f := fun y => (chi0 (c - y) : ℂ) *
          ftπ phiM (v - τ * c - (1 - τ) * y)) ?_ j, norm_zero]
      · have := A1_nonneg; positivity
      · have hcont : Continuous fun y : ℝ => |c - y| := (continuous_const.sub continuous_id).abs
        have hev : ∀ᶠ y in nhds u, 1 < |c - y| := hcont.continuousAt (Ioi_mem_nhds hcu)
        filter_upwards [hev] with y hy
        rw [chi0_eq_zero hy.le]; simp
    · push Not at hcu
      have h2 : 1 ≤ 2 / (1 + |c - u|) := by rw [le_div_iff₀ hp]; linarith
      have hg := norm_iteratedDeriv_mul_gevrey hC hF (a := Real.exp 4)
        (b := KFP / (1 + |v - u - τ * (c - u)|) ^ 3) (by positivity) (by positivity) A1_nonneg
        (fun i => (norm_iteratedDeriv_sub_le contDiff_chi0c c u i).trans
          ((norm_iteratedDeriv_chi0c_le i (c - u)).trans (by
            have := pow_le_pow_left₀ Achi_nonneg Achi_le_A1 i
            gcongr)))
        (fun i => by
          refine (norm_iteratedDeriv_comp_affine_le contDiff_FP hτ1 _ u i).trans ?_
          have e : v - τ * c - (1 - τ) * u = v - u - τ * (c - u) := by ring
          rw [e]
          refine (FP_deriv_bound.2.2 i _).trans ?_
          have := geom_le_gevrey (K := KFP / (1 + |v - u - τ * (c - u)|) ^ 3) (by positivity)
            FP_deriv_bound.2.1 BFP_le_A1 i
          calc KFP * BFP ^ i / (1 + |v - u - τ * (c - u)|) ^ 3
              = KFP / (1 + |v - u - τ * (c - u)|) ^ 3 * BFP ^ i := by ring
            _ ≤ _ := this) j
      calc _ ≤ 4 * Real.exp 4 * (KFP / (1 + |v - u - τ * (c - u)|) ^ 3) * A1 ^ j *
            (Nat.factorial (2 * j) : ℝ) := hg
        _ = 1 * (4 * Real.exp 4 * KFP * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) * A1 ^ j *
            (Nat.factorial (2 * j) : ℝ)) := by ring
        _ ≤ (2 / (1 + |c - u|)) * (4 * Real.exp 4 * KFP * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) *
            A1 ^ j * (Nat.factorial (2 * j) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right h2 ?_
          have := A1_nonneg; positivity
        _ = _ := by ring
  -- the `Φ M₀(v - c)` part
  have hpc : ‖iteratedDeriv j (fun y => phiR (c - y) * M0 (v - c)) u‖ ≤
      CPhi / (1 + |c - u|) * (KM0 / (1 + |v - c|) ^ 3) * A1 ^ j * (Nat.factorial (2 * j) : ℝ) := by
    have e : (fun y => phiR (c - y) * M0 (v - c)) = fun y => M0 (v - c) * phiR (c - y) := by
      funext y; ring
    rw [e, iteratedDeriv_const_mul _ (ContDiff.cdAt hP j u), norm_mul]
    calc ‖M0 (v - c)‖ * ‖iteratedDeriv j (fun y => phiR (c - y)) u‖
        ≤ KM0 / (1 + |v - c|) ^ 3 * (CPhi / (1 + |c - u|) * A1 ^ j *
            (Nat.factorial (2 * j) : ℝ)) :=
          mul_le_mul (by simpa using norm_iteratedDeriv_M0_le 0 (v - c)) (hPd j) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  -- the `Φ M₀(v - u)` part
  have hpm : ‖iteratedDeriv j (fun y => phiR (c - y) * M0 (v - y)) u‖ ≤
      4 * (CPhi / (1 + |c - u|)) * (KM0 / (1 + |v - u|) ^ 3) * A1 ^ j *
        (Nat.factorial (2 * j) : ℝ) :=
    norm_iteratedDeriv_mul_gevrey hP hM (by positivity) (by positivity) A1_nonneg hPd
      (fun i => (norm_iteratedDeriv_sub_le contDiff_M0 v u i).trans
        (norm_iteratedDeriv_M0_le i (v - u))) j
  calc _ ≤ ‖iteratedDeriv j (fun y => (chi0 (c - y) : ℂ) * ftπ phiM (v - τ * c - (1 - τ) * y)) u‖
        + (‖iteratedDeriv j (fun y => phiR (c - y) * M0 (v - c)) u‖ +
          ‖iteratedDeriv j (fun y => phiR (c - y) * M0 (v - y)) u‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ 8 * Real.exp 4 * KFP / (1 + |c - u|) * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) *
          A1 ^ j * (Nat.factorial (2 * j) : ℝ) +
        (CPhi / (1 + |c - u|) * (KM0 / (1 + |v - c|) ^ 3) * A1 ^ j * (Nat.factorial (2 * j) : ℝ) +
          4 * (CPhi / (1 + |c - u|)) * (KM0 / (1 + |v - u|) ^ 3) * A1 ^ j *
            (Nat.factorial (2 * j) : ℝ)) := add_le_add hker (add_le_add hpc hpm)
    _ = A1 ^ j * (Nat.factorial (2 * j) : ℝ) / (1 + |c - u|) *
          (8 * Real.exp 4 * KFP * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) +
            CPhi * KM0 * (1 / (1 + |v - c|) ^ 3) + 4 * CPhi * KM0 * (1 / (1 + |v - u|) ^ 3)) := by
        field_simp
        ring
    _ ≤ A1 ^ j * (Nat.factorial (2 * j) : ℝ) / (1 + |c - u|) *
          (CE * (1 / (1 + |v - u - τ * (c - u)|) ^ 3) + CE * (1 / (1 + |v - c|) ^ 3) +
            CE * (1 / (1 + |v - u|) ^ 3)) := by
        have h0 : 0 ≤ Real.exp 4 * KFP := by positivity
        have h0' : 0 ≤ CPhi * KM0 := by positivity
        have h1 : 8 * Real.exp 4 * KFP ≤ CE := by unfold CE; have := kerM_bound.1; nlinarith
        have h2 : CPhi * KM0 ≤ CE := by unfold CE; have := kerM_bound.1; nlinarith
        have h3 : 4 * CPhi * KM0 ≤ CE := by unfold CE; have := kerM_bound.1; nlinarith
        have := A1_nonneg
        gcongr
    _ = _ := by ring

end Diagonal

section Integrated

theorem one_add_enorm_rpow_eq (x a : ℝ) :
    ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ a = ENNReal.ofReal ((1 + |x|) ^ a) := by
  rw [one_add_enorm_eq, ENNReal.ofReal_rpow_of_pos (by positivity)]

/-- `(1 + |y + z|)^a ≤ (1 + |y|)^a (1 + |z|)^a` for `a ≥ 0`. -/
theorem one_add_abs_add_rpow_le {a : ℝ} (h0 : 0 ≤ a) (y z : ℝ) :
    (1 + |y + z|) ^ a ≤ (1 + |y|) ^ a * (1 + |z|) ^ a := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ h0
  nlinarith [abs_add_le y z, abs_nonneg y, abs_nonneg z]

/-- `x^a ≤ x` for `x ≥ 1` and `a ≤ 1`. -/
theorem rpow_le_self_of_one_le {x a : ℝ} (hx : 1 ≤ x) (h1 : a ≤ 1) : x ^ a ≤ x := by
  calc x ^ a ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1
    _ = x := Real.rpow_one x

theorem decay3_eq (w : ℝ) :
    (1 + |w|) * (1 / (1 + |w|) ^ 3) = (1 + |w|) ^ (-(2 : ℝ)) := by
  have hp : 0 < 1 + |w| := by positivity
  rw [Real.rpow_neg hp.le, show ((1 + |w|) ^ (2 : ℝ)) = (1 + |w|) ^ (2 : ℕ) by norm_cast]
  field_simp

/-- **A weighted shifted cubic decay**: `∫ (1+|v+g|)^a (1+|v-p|)^{-3} dv ≤ Ir 2 (1+|p+g|)^a`
for `0 ≤ a ≤ 1`. -/
theorem lintegral_wt_decay3_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (p g : ℝ) :
    ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v + g|) ^ a * (1 / (1 + |v - p|) ^ 3)) ≤
      ENNReal.ofReal (Ir 2 * (1 + |p + g|) ^ a) := by
  have hpt : ∀ v : ℝ, (1 + |v + g|) ^ a * (1 / (1 + |v - p|) ^ 3) ≤
      (1 + |p + g|) ^ a * (1 + |v - p|) ^ (-(2 : ℝ)) := fun v => by
    have e : v + g = (v - p) + (p + g) := by ring
    rw [e, ← decay3_eq]
    calc (1 + |v - p + (p + g)|) ^ a * (1 / (1 + |v - p|) ^ 3)
        ≤ ((1 + |v - p|) ^ a * (1 + |p + g|) ^ a) * (1 / (1 + |v - p|) ^ 3) :=
          mul_le_mul_of_nonneg_right (one_add_abs_add_rpow_le h0 _ _) (by positivity)
      _ ≤ ((1 + |v - p|) * (1 + |p + g|) ^ a) * (1 / (1 + |v - p|) ^ 3) := by
          gcongr
          exact rpow_le_self_of_one_le (by linarith [abs_nonneg (v - p)]) h1
      _ = _ := by ring
  calc ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v + g|) ^ a * (1 / (1 + |v - p|) ^ 3))
      ≤ ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |p + g|) ^ a) *
          ENNReal.ofReal ((1 + |v - p|) ^ (-(2 : ℝ))) := lintegral_mono fun v => by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt v)
    _ = ENNReal.ofReal ((1 + |p + g|) ^ a) *
          ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v - p|) ^ (-(2 : ℝ))) :=
        lintegral_const_mul _ (by fun_prop)
    _ = ENNReal.ofReal ((1 + |p + g|) ^ a) * ENNReal.ofReal (Ir 2) := by
        rw [lintegral_sub_right_eq_self (fun v : ℝ => ENNReal.ofReal ((1 + |v|) ^ (-(2 : ℝ)))) p,
          lintegral_Ir_eq (by norm_num)]
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_comm]

theorem lintegral_ind01r : ∫⁻ τ : ℝ, ENNReal.ofReal (ind01r τ) = 1 := by
  have : (fun τ : ℝ => ENNReal.ofReal (ind01r τ)) =
      (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext τ
    by_cases h : τ ∈ Icc (0 : ℝ) 1 <;> simp [ind01r, h]
  rw [this, lintegral_indicator_const measurableSet_Icc]
  simp

theorem Ir2_nonneg : 0 ≤ Ir 2 := ENNReal.toReal_nonneg

@[fun_prop] theorem measurable_ind01r : Measurable ind01r :=
  measurable_const.indicator measurableSet_Icc

/-- **The weighted `x`-derivative bounds of `gE`** (Case 1 of Proposition 5.1):
`∫ (1+|λ|)^a |∂_x^j gE(x; λ, τ)| dλ dτ ≤ 2 C_E Ir(2) A₁^j (2j)! (1+|x|)^{a-1}`. -/
theorem lintegral_gE_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (j : ℕ) (x : ℝ) :
    ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a * ‖iteratedDeriv j (fun y => gE y q) x‖ₑ ≤
      ENNReal.ofReal (2 * CE * Ir 2 * A1 ^ j * (Nat.factorial (2 * j) : ℝ) *
        (1 + |x|) ^ (a - 1)) := by
  set K : ℝ := CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) with hK
  have hK0 : 0 ≤ K := by have := CE_nonneg; have := A1_nonneg; positivity
  have hp : 0 < 1 + |x| := by positivity
  have hpt : ∀ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a * ‖iteratedDeriv j (fun y => gE y q) x‖ₑ ≤
      ENNReal.ofReal (K / (1 + |x|)) * (ENNReal.ofReal (ind01r q.2) *
        (ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - 0|) ^ 3)) +
          ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - x|) ^ 3)))) := fun q => by
    rw [one_add_enorm_rpow_eq, ← ofReal_norm]
    have hb := norm_iteratedDeriv_gE_le j x q
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (ind01r_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [add_zero, sub_zero]
    calc (1 + |q.1|) ^ a * ‖iteratedDeriv j (fun y => gE y q) x‖
        ≤ (1 + |q.1|) ^ a * (K * ind01r q.2 / (1 + |x|) *
            (1 / (1 + |q.1|) ^ 3 + 1 / (1 + |q.1 - x|) ^ 3)) := by
          gcongr
      _ = _ := by ring
  have hmeas : Measurable fun v : ℝ =>
      ENNReal.ofReal ((1 + |v + 0|) ^ a * (1 / (1 + |v - 0|) ^ 3)) +
        ENNReal.ofReal ((1 + |v + 0|) ^ a * (1 / (1 + |v - x|) ^ 3)) := by fun_prop
  have hmeas2 : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (ind01r q.2) *
      (ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - 0|) ^ 3)) +
        ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - x|) ^ 3))) :=
    (measurable_ind01r.ennreal_ofReal.comp measurable_snd).mul (hmeas.comp measurable_fst)
  calc ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1‖ₑ) ^ a * ‖iteratedDeriv j (fun y => gE y q) x‖ₑ
      ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (K / (1 + |x|)) * (ENNReal.ofReal (ind01r q.2) *
          (ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - 0|) ^ 3)) +
            ENNReal.ofReal ((1 + |q.1 + 0|) ^ a * (1 / (1 + |q.1 - x|) ^ 3)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (K / (1 + |x|)) * ((∫⁻ τ : ℝ, ENNReal.ofReal (ind01r τ)) *
          ∫⁻ v : ℝ, (ENNReal.ofReal ((1 + |v + 0|) ^ a * (1 / (1 + |v - 0|) ^ 3)) +
            ENNReal.ofReal ((1 + |v + 0|) ^ a * (1 / (1 + |v - x|) ^ 3)))) := by
        rw [lintegral_const_mul _ hmeas2, Measure.volume_eq_prod,
          lintegral_prod_symm _ hmeas2.aemeasurable]
        congr 1
        rw [← lintegral_mul_const _ (measurable_ind01r.ennreal_ofReal)]
        refine lintegral_congr fun τ => ?_
        simp only
        rw [lintegral_const_mul _ hmeas]
    _ ≤ ENNReal.ofReal (K / (1 + |x|)) * (1 * (ENNReal.ofReal (Ir 2 * (1 + |0 + 0|) ^ a) +
          ENNReal.ofReal (Ir 2 * (1 + |x + 0|) ^ a))) := by
        rw [lintegral_ind01r, lintegral_add_left (by fun_prop)]
        gcongr
        · exact lintegral_wt_decay3_le h0 h1 0 0
        · exact lintegral_wt_decay3_le h0 h1 x 0
    _ ≤ ENNReal.ofReal (2 * CE * Ir 2 * A1 ^ j * (Nat.factorial (2 * j) : ℝ) *
          (1 + |x|) ^ (a - 1)) := by
        simp only [add_zero, abs_zero, one_mul, Real.one_rpow, mul_one]
        rw [← ENNReal.ofReal_add Ir2_nonneg (by have := Ir2_nonneg; positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hxa : 1 ≤ (1 + |x|) ^ a := Real.one_le_rpow (by linarith [abs_nonneg x]) h0
        have hsplit : (1 + |x|) ^ (a - 1) = (1 + |x|) ^ a / (1 + |x|) := by
          rw [Real.rpow_sub hp, Real.rpow_one]
        rw [hsplit, hK]
        have hI := Ir2_nonneg
        have hC := CE_nonneg
        have hA : 0 ≤ A1 ^ j * (Nat.factorial (2 * j) : ℝ) := by have := A1_nonneg; positivity
        rw [div_mul_eq_mul_div, mul_div_assoc', le_div_iff₀ hp, div_mul_cancel₀ _ hp.ne']
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC hA) hI) (sub_nonneg.2 hxa)]

end Integrated

section IntegratedDiag

/-- The explicit majorant of `|∂_u^j gE(c-u; v-u, τ)|` (`norm_iteratedDeriv_gED_le`). -/
@[expose] noncomputable def gEDbd (j : ℕ) (c u : ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) * ind01r q.2 / (1 + |c - u|) *
    (1 / (1 + |q.1 - (u + q.2 * (c - u))|) ^ 3 + 1 / (1 + |q.1 - c|) ^ 3 +
      1 / (1 + |q.1 - u|) ^ 3))

theorem enorm_iteratedDeriv_gED_le_bd (j : ℕ) (c u : ℝ) (q : ℝ × ℝ) :
    ‖iteratedDeriv j (fun y => gE (c - y) (q.1 - y, q.2)) u‖ₑ ≤ gEDbd j c u q := by
  rw [← ofReal_norm, gEDbd]
  refine ENNReal.ofReal_le_ofReal ((norm_iteratedDeriv_gED_le j c u q.1 q.2).trans_eq ?_)
  congr 4
  ring_nf

theorem measurable_gEDbd (j : ℕ) :
    Measurable fun p : ℝ × ℝ × (ℝ × ℝ) => gEDbd j p.1 p.2.1 p.2.2 := by
  unfold gEDbd
  fun_prop

/-- The weighted integral of the diagonal majorant against any dominating constant `X`. -/
theorem lintegral_gEDbd_le_X {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (j : ℕ) (c u g X : ℝ)
    (hX0 : 0 ≤ X) (hX1 : ∀ τ ∈ Icc (0 : ℝ) 1, (1 + |u + τ * (c - u) + g|) ^ a ≤ X)
    (hX2 : (1 + |c + g|) ^ a ≤ X) (hX3 : (1 + |u + g|) ^ a ≤ X) :
    ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a * gEDbd j c u q ≤
      ENNReal.ofReal (CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) / (1 + |c - u|) *
        (3 * Ir 2 * X)) := by
  set K : ℝ := CE * A1 ^ j * (Nat.factorial (2 * j) : ℝ) with hK
  have hK0 : 0 ≤ K := by have := CE_nonneg; have := A1_nonneg; positivity
  have hp : 0 < 1 + |c - u| := by positivity
  -- the integrand bound
  set F : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (ind01r q.2) *
    (ENNReal.ofReal (K / (1 + |c - u|)) *
      (ENNReal.ofReal ((1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - (u + q.2 * (c - u))|) ^ 3)) +
        ENNReal.ofReal ((1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - c|) ^ 3)) +
        ENNReal.ofReal ((1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - u|) ^ 3)))) with hF
  have hFm : Measurable F := by simp only [hF]; fun_prop
  have hpt : ∀ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a * gEDbd j c u q ≤ F q := fun q => by
    have hi := ind01r_nonneg q.2
    have hFq : F q = ENNReal.ofReal (ind01r q.2 * (K / (1 + |c - u|) *
        ((1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - (u + q.2 * (c - u))|) ^ 3) +
          (1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - c|) ^ 3) +
          (1 + |q.1 + g|) ^ a * (1 / (1 + |q.1 - u|) ^ 3)))) := by
      simp only [hF]
      conv_rhs => rw [ENNReal.ofReal_mul hi, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [hFq, one_add_enorm_rpow_eq, gEDbd, ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq ?_
    congr 1
    simp only [hK]
    field_simp
  -- the inner integral
  have hinner : ∀ τ : ℝ, ∫⁻ v : ℝ, F (v, τ) ≤
      ENNReal.ofReal (ind01r τ) * ENNReal.ofReal (K / (1 + |c - u|) * (3 * Ir 2 * X)) := by
    intro τ
    simp only [hF]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
    by_cases hτ : τ ∈ Icc (0 : ℝ) 1
    swap
    · simp [ind01r, Set.indicator_of_notMem hτ]
    refine mul_le_mul' le_rfl ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' le_rfl ?_
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
    have b1 : Ir 2 * (1 + |u + τ * (c - u) + g|) ^ a ≤ Ir 2 * X :=
      mul_le_mul_of_nonneg_left (hX1 τ hτ) Ir2_nonneg
    have b2 : Ir 2 * (1 + |c + g|) ^ a ≤ Ir 2 * X := mul_le_mul_of_nonneg_left hX2 Ir2_nonneg
    have b3 : Ir 2 * (1 + |u + g|) ^ a ≤ Ir 2 * X := mul_le_mul_of_nonneg_left hX3 Ir2_nonneg
    have hI := Ir2_nonneg
    calc (∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v + g|) ^ a * (1 / (1 + |v - (u + τ * (c - u))|) ^ 3))) +
          (∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v + g|) ^ a * (1 / (1 + |v - c|) ^ 3))) +
          (∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v + g|) ^ a * (1 / (1 + |v - u|) ^ 3)))
        ≤ ENNReal.ofReal (Ir 2 * X) + ENNReal.ofReal (Ir 2 * X) + ENNReal.ofReal (Ir 2 * X) := by
          gcongr
          · exact (lintegral_wt_decay3_le h0 h1 _ g).trans (ENNReal.ofReal_le_ofReal b1)
          · exact (lintegral_wt_decay3_le h0 h1 c g).trans (ENNReal.ofReal_le_ofReal b2)
          · exact (lintegral_wt_decay3_le h0 h1 u g).trans (ENNReal.ofReal_le_ofReal b3)
      _ = ENNReal.ofReal (3 * Ir 2 * X) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a * gEDbd j c u q
      ≤ ∫⁻ q, F q := lintegral_mono hpt
    _ = ∫⁻ τ : ℝ, ∫⁻ v : ℝ, F (v, τ) := by
        rw [Measure.volume_eq_prod, lintegral_prod_symm _ hFm.aemeasurable]
    _ ≤ ∫⁻ τ : ℝ, ENNReal.ofReal (ind01r τ) *
          ENNReal.ofReal (K / (1 + |c - u|) * (3 * Ir 2 * X)) := lintegral_mono hinner
    _ = ENNReal.ofReal (K / (1 + |c - u|) * (3 * Ir 2 * X)) := by
        rw [lintegral_mul_const _ measurable_ind01r.ennreal_ofReal, lintegral_ind01r, one_mul]

/-- **The weighted integral of the diagonal majorant** (Lemma G, DH21 (propertyG)):
`∫ (1+|λ+g|)^a gEDbd ≤ 3 C_E Ir(2) A₁^j (2j)! (1+|u+g|)^a (1+|c-u|)^{a-1}`. -/
theorem lintegral_gEDbd_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (j : ℕ) (c u g : ℝ) :
    ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a * gEDbd j c u q ≤
      ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ j * (Nat.factorial (2 * j) : ℝ) *
        ((1 + |u + g|) ^ a * (1 + |c - u|) ^ (a - 1))) := by
  have hp : 0 < 1 + |c - u| := by positivity
  set X : ℝ := (1 + |u + g|) ^ a * (1 + |c - u|) ^ a with hX
  refine (lintegral_gEDbd_le_X h0 h1 j c u g X (by positivity) (fun τ hτ => ?_) ?_ ?_).trans_eq ?_
  · have hτa : |τ * (c - u)| ≤ |c - u| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (by
        rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2])
    have e : u + τ * (c - u) + g = (u + g) + τ * (c - u) := by ring
    rw [e, hX]
    refine (one_add_abs_add_rpow_le h0 _ _).trans ?_
    gcongr
  · have e : c + g = (u + g) + (c - u) := by ring
    rw [e, hX]
    exact one_add_abs_add_rpow_le h0 _ _
  · rw [hX]
    exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (by linarith [abs_nonneg (c - u)]) h0)
  · congr 1
    have hsplit : (1 + |c - u|) ^ (a - 1) = (1 + |c - u|) ^ a / (1 + |c - u|) := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    rw [hsplit, hX]
    field_simp

/-- `(1 + |y + z|)^a ≤ (1 + |y|)^a + (1 + |z|)^a` for `0 ≤ a ≤ 1`. -/
theorem one_add_abs_add_rpow_le_add {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (y z : ℝ) :
    (1 + |y + z|) ^ a ≤ (1 + |y|) ^ a + (1 + |z|) ^ a := by
  calc (1 + |y + z|) ^ a ≤ ((1 + |y|) + (1 + |z|)) ^ a := by
        refine Real.rpow_le_rpow (by positivity) ?_ h0
        linarith [abs_add_le y z, abs_nonneg z]
    _ ≤ (1 + |y|) ^ a + (1 + |z|) ^ a :=
        Real.rpow_add_le_add_rpow (by positivity) (by positivity) h0 h1

/-- **The split weighted integral of the diagonal majorant** (class `R` version of DH21 (propertyG)):
`∫ (1+|λ+g|)^a gEDbd ≤ 6 C_E Ir(2) A₁^j (2j)! ((1+|u+g|)^a (1+|c-u|)^{-1} + (1+|c-u|)^{a-1})`; the weight
falls on one denominator at a time (DH23 L966–L969). -/
theorem lintegral_gEDbd_le_split {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (j : ℕ) (c u g : ℝ) :
    ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a * gEDbd j c u q ≤
      ENNReal.ofReal (6 * CE * Ir 2 * A1 ^ j * (Nat.factorial (2 * j) : ℝ) *
        ((1 + |u + g|) ^ a / (1 + |c - u|) + (1 + |c - u|) ^ (a - 1))) := by
  have hp : 0 < 1 + |c - u| := by positivity
  set X : ℝ := 2 * ((1 + |u + g|) ^ a + (1 + |c - u|) ^ a) with hX
  have hY1 : (1 + |u + g|) ^ a ≤ X := by
    have h2 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |c - u|) a
    have h3 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |u + g|) a
    rw [hX]; linarith
  refine (lintegral_gEDbd_le_X h0 h1 j c u g X (by positivity) (fun τ hτ => ?_) ?_ hY1).trans_eq ?_
  · have hτa : |τ * (c - u)| ≤ |c - u| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (by
        rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2])
    have e : u + τ * (c - u) + g = (u + g) + τ * (c - u) := by ring
    rw [e]
    refine (one_add_abs_add_rpow_le_add h0 h1 _ _).trans ?_
    have : (1 + |τ * (c - u)|) ^ a ≤ (1 + |c - u|) ^ a := by gcongr
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |u + g|) a
    rw [hX]; linarith
  · have e : c + g = (u + g) + (c - u) := by ring
    rw [e]
    refine (one_add_abs_add_rpow_le_add h0 h1 _ _).trans ?_
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |u + g|) a
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |c - u|) a
    rw [hX]; linarith
  · congr 1
    have hsplit : (1 + |c - u|) ^ (a - 1) = (1 + |c - u|) ^ a / (1 + |c - u|) := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    rw [hsplit, hX]
    field_simp
    ring

/-- **The weighted diagonal derivative bounds of `gE`** (Lemma G, DH21 (propertyG)):
`∫ (1+|λ+g|)^a |∂_u^j gE(c-u; λ-u, τ)| dλ dτ ≤ 3 C_E Ir(2) A₁^j (2j)! (1+|u+g|)^a (1+|c-u|)^{a-1}`. -/
theorem lintegral_gED_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (j : ℕ) (c u g : ℝ) :
    ∫⁻ q : ℝ × ℝ, ((1 : ℝ≥0∞) + ‖q.1 + g‖ₑ) ^ a *
        ‖iteratedDeriv j (fun y => gE (c - y) (q.1 - y, q.2)) u‖ₑ ≤
      ENNReal.ofReal (3 * CE * Ir 2 * A1 ^ j * (Nat.factorial (2 * j) : ℝ) *
        ((1 + |u + g|) ^ a * (1 + |c - u|) ^ (a - 1))) :=
  (lintegral_mono fun q => mul_le_mul' le_rfl (enorm_iteratedDeriv_gED_le_bd j c u q)).trans
    (lintegral_gEDbd_le h0 h1 j c u g)

end IntegratedDiag

end WaveTurbulence.ClassJR

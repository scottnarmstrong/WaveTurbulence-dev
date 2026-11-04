/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Marginal
public import WaveTurbulence.Foundations.Cancel.Pieces
public import WaveTurbulence.Foundations.ClassJR.CompJJSetup
public import WaveTurbulence.Foundations.ClassJR.IRI3

/-!
# Class `J` and class `R` operators applied to an exponential are integrable (DH21 §7.1)

DH21 Lemmas 7.1–7.3 assert that `K = I(e^{πiλs})(t)` is in `L¹` of its variables `α[W]` when `I` is a class `J`
plus class `R` operator (DH21 L1720: "by repeating the proof of Proposition 5.1, we know that `K ∈ L¹`"). The
reason is plain:
* a basic class `J` kernel `∫ m(α, γ) J_{ℓ;γ₁,γ₂} dγ` is bounded by `∫ |m(α, γ)| dγ`, integrable in `α`;
* a basic class `R` kernel applied to `e^{πiλs}` is
  `∫ m(α', γ) χ_∞(a + γ₃)/(a + γ₃) e^{πi(b+γ₁)t} E(γ₂ + λ - b, t) dγ` with `a, b` affine in the special
  variable `α₁` (coefficient `ε = ±1`), and `|χ_∞(y)/y| ≲ ⟨y⟩⁻¹`, `|E(x, t)| ≲ ⟨x⟩⁻¹` give an integrable
  majorant in `α₁` (`lintegral_decay_pair`).

Main result: `mJR_mInt_volterra` (class `J` plus class `R` in the variables `W`, applied to an exponential,
is integrable over `α[W]`).
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology ENNReal

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR WaveTurbulence.Fourier

/-! ### Scalar bounds -/

theorem norm_eInt_le_one {x v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ‖eInt x v‖ ≤ 1 := by
  unfold eInt
  have hb : ∀ u ∈ uIoc 0 v, ‖cexp (π * I * (x * u))‖ ≤ 1 := fun u _ => by
    exact_mod_cast (norm_cexp_piI (x * u)).le
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  rw [sub_zero, abs_of_nonneg hv.1, one_mul]; exact hv.2

/-- `(1 + |x|) |E(x, v)| ≤ 2` for `v ∈ [0, 1]`. -/
theorem norm_eInt_mul_le {x v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ‖eInt x v‖ * (1 + |x|) ≤ 2 := by
  have h1 := norm_eInt_le_one (x := x) hv
  by_cases hx : x = 0
  · subst hx; simp; linarith
  have h2 : ‖eInt x v‖ * |x| ≤ 1 := by
    rw [eInt_eq_of_ne hx, norm_div]
    have hπ : 0 < π := Real.pi_pos
    have hnum : ‖cexp (π * I * (x * v)) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [show (π : ℂ) * I * (x * v) = π * I * ((x * v : ℝ) : ℂ) by push_cast; ring, norm_cexp_piI]
      norm_num
    have hden : ‖(π : ℂ) * I * x‖ = π * |x| := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hπ, mul_one]
    rw [hden]
    have hxpos : 0 < |x| := abs_pos.2 hx
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    calc ‖cexp (π * I * (x * v)) - 1‖ * |x| ≤ 2 * |x| :=
          mul_le_mul_of_nonneg_right hnum (abs_nonneg _)
      _ ≤ π * |x| := mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) (abs_nonneg _)
  nlinarith

/-- `(1 + |y|) |χ_∞(y)/y| ≤ CPhi`. -/
theorem norm_chiInvR_mul_le (y : ℝ) : ‖(chiInvR y : ℂ)‖ * (1 + |y|) ≤ CPhi := by
  have := chiInvR_gevrey 0 y
  simp only [iteratedDeriv_zero, pow_zero, mul_one, Nat.mul_zero, Nat.factorial_zero,
    Nat.cast_one] at this
  rw [Complex.norm_real, mul_comm]
  unfold CPhi
  linarith

theorem inv_one_add_abs_sq_le (u : ℝ) : ((1 + |u|)⁻¹) ^ 2 ≤ (1 + u ^ 2)⁻¹ := by
  rw [inv_pow]
  refine inv_anti₀ (by positivity) ?_
  nlinarith [abs_nonneg u, sq_abs u]

/-- **The integral of a product of two decays** `∫ ⟨x - a⟩⁻¹ ⟨x - b⟩⁻¹ dx ≤ π`. -/
theorem lintegral_decay_pair (a b : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((1 + |x - a|)⁻¹ * (1 + |x - b|)⁻¹) ≤ ENNReal.ofReal π := by
  have hle : ∀ x : ℝ, (1 + |x - a|)⁻¹ * (1 + |x - b|)⁻¹ ≤
      ((1 + (x - a) ^ 2)⁻¹ + (1 + (x - b) ^ 2)⁻¹) / 2 := by
    intro x
    have h1 := inv_one_add_abs_sq_le (x - a)
    have h2 := inv_one_add_abs_sq_le (x - b)
    have : (1 + |x - a|)⁻¹ * (1 + |x - b|)⁻¹ ≤ (((1 + |x - a|)⁻¹) ^ 2 + ((1 + |x - b|)⁻¹) ^ 2) / 2 := by
      nlinarith [sq_nonneg ((1 + |x - a|)⁻¹ - (1 + |x - b|)⁻¹)]
    linarith
  have hia : Integrable fun x : ℝ => (1 + (x - a) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_sub_right a
  have hib : Integrable fun x : ℝ => (1 + (x - b) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_sub_right b
  have hint : Integrable fun x : ℝ => ((1 + (x - a) ^ 2)⁻¹ + (1 + (x - b) ^ 2)⁻¹) / 2 :=
    (hia.add hib).div_const 2
  calc ∫⁻ x, ENNReal.ofReal ((1 + |x - a|)⁻¹ * (1 + |x - b|)⁻¹)
      ≤ ∫⁻ x, ENNReal.ofReal (((1 + (x - a) ^ 2)⁻¹ + (1 + (x - b) ^ 2)⁻¹) / 2) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
    _ = ENNReal.ofReal (∫ x, ((1 + (x - a) ^ 2)⁻¹ + (1 + (x - b) ^ 2)⁻¹) / 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)).symm
    _ = ENNReal.ofReal π := by
        rw [MeasureTheory.integral_div, integral_add hia hib, integral_sub_right_eq_self
          (fun x => (1 + x ^ 2)⁻¹) a, integral_sub_right_eq_self (fun x => (1 + x ^ 2)⁻¹) b,
          integral_univ_inv_one_add_sq]
        ring_nf

/-! ### Basic class `J` kernels -/

/-- The exponential `e^{πiλs}`. -/
@[expose] noncomputable def expF (lam s : ℝ) : ℂ := cexp (π * I * (lam * s))

theorem norm_expF (lam s : ℝ) : ‖expF lam s‖ = 1 := by
  unfold expF; exact_mod_cast norm_cexp_piI (lam * s)

@[fun_prop] theorem continuous_expF (lam : ℝ) : Continuous (expF lam) := by unfold expF; fun_prop

section Basic

variable {ι : Type*} [Fintype ι]

theorem norm_JSym_kernel_le (R : JSym ι) (β : ι → ℝ) (t s : ℝ) :
    ‖R.kernel β t s‖ ≤ ∫ γ, ‖R.m β γ‖ := by
  unfold JSym.kernel
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
  congr 1; funext γ; rw [norm_mul, norm_jker, mul_one]

theorem norm_volterra_le_of {K : ℝ → ℝ → ℂ} {C t : ℝ} (hK : ∀ s, ‖K t s‖ ≤ C) (hC : 0 ≤ C)
    (lam : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖volterra K (expF lam) t‖ ≤ C := by
  unfold volterra
  have hb : ∀ s ∈ uIoc 0 t, ‖K t s * expF lam s‖ ≤ C := fun s _ => by
    rw [norm_mul, norm_expF, mul_one]; exact hK s
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  rw [sub_zero, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_right hC ht.2

theorem stronglyMeasurable_volterra {X : Type*} [MeasurableSpace X] {K : X → ℝ → ℝ → ℂ} {t : ℝ}
    (hK : StronglyMeasurable fun p : X × ℝ => K p.1 t p.2) (g : ℝ → ℂ) (hg : Continuous g) :
    StronglyMeasurable fun x => volterra (K x) g t := by
  have hF : StronglyMeasurable fun p : X × ℝ => K p.1 t p.2 * g p.2 :=
    hK.mul (hg.measurable.comp measurable_snd).stronglyMeasurable
  unfold volterra
  simp only [intervalIntegral]
  exact (hF.integral_prod_right' (ν := volume.restrict (Ioc 0 t))).sub
    (hF.integral_prod_right' (ν := volume.restrict (Ioc t 0)))

theorem stronglyMeasurable_JSym_kernel (R : JSym ι) (hR : SymReg R.m) (t : ℝ) :
    StronglyMeasurable fun p : (ι → ℝ) × ℝ => R.kernel p.1 t p.2 := by
  unfold JSym.kernel
  have hm : StronglyMeasurable fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ) => R.m q.1.1 q.2 :=
    hR.meas.comp_measurable (measurable_fst.fst.prodMk measurable_snd)
  have hj : StronglyMeasurable fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ) =>
      jker (bundle R.y q.1.1) q.2.1 q.2.2 t q.1.2 := by
    refine Continuous.stronglyMeasurable ?_
    unfold jker
    have := continuous_bundle R.y
    fun_prop
  exact (hm.mul hj).integral_prod_right'

/-- `∫∫ |m| ≤ N` for a basic class `J` symbol with bound `N`. -/
theorem jsym_lintegral_le {R : JSym ι} {θ A N : ℝ} (hR : R.Bound θ A N) (hθ : 0 ≤ θ) :
    ∫⁻ β, ∫⁻ γ, ‖R.m β γ‖ₑ ≤ ENNReal.ofReal N := by
  have h := hR.norm 0
  unfold jNorm gev at h
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one] at h
  refine le_trans (lintegral_mono fun β => lintegral_mono fun γ => ?_) h
  rw [dnorm_zero]
  exact le_mul_of_one_le_left bot_le (one_le_wJ hθ β γ.1)

/-- **A basic class `J` operator applied to `e^{πiλs}` is integrable in its variables.** -/
theorem integrable_volterra_JSym {R : JSym ι} {θ A N : ℝ} (hR : R.Bound θ A N) (hθ : 0 ≤ θ)
    (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable fun β => volterra (R.kernel β) (expF lam) t := by
  have hmeas := stronglyMeasurable_volterra (stronglyMeasurable_JSym_kernel R hR.reg t)
    (expF lam) (continuous_expF lam)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := N))
  refine le_trans (lintegral_mono fun β => ?_) (jsym_lintegral_le hR hθ)
  have h1 := norm_volterra_le_of (K := R.kernel β) (t := t)
    (fun s => norm_JSym_kernel_le R β t s) (integral_nonneg fun _ => norm_nonneg _) lam ht
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hR.reg.integrable β), ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h1

/-! ### Basic class `R` kernels -/

/-- The denominator variable `a = ℓ₁ + εα₁` of a basic class `R` kernel. -/
@[expose] noncomputable def raR (R : RSym ι) (β : Option ι → ℝ) : ℝ :=
  bundle R.y₁ (nsp β) + R.ε * β none

/-- The phase variable `b = ℓ₂ + εα₁` of a basic class `R` kernel. -/
@[expose] noncomputable def rbR (R : RSym ι) (β : Option ι → ℝ) : ℝ :=
  bundle R.y₂ (nsp β) + R.ε * β none

theorem jker_mul_expF (b γ₁ γ₂ lam t s : ℝ) :
    jker b γ₁ γ₂ t s * expF lam s =
      cexp (π * I * ((b + γ₁) * t)) * cexp (π * I * ((γ₂ + lam - b) * s)) := by
  simp only [jker, expF, ← Complex.exp_add]
  congr 1; ring

/-- **A basic class `R` kernel applied to `e^{πiλs}`** (Fubini). -/
theorem volterra_RSym_exp (R : RSym ι) (hR : SymReg R.m) (β : Option ι → ℝ) (lam t : ℝ) :
    volterra (R.kernel β) (expF lam) t = ∫ γ : ℝ × ℝ × ℝ, R.m (nsp β) γ *
      (chiInvR (raR R β + γ.2.2) : ℂ) *
        (cexp (π * I * ((rbR R β + γ.1) * t)) * eInt (γ.2.1 + lam - rbR R β) t) := by
  unfold volterra RSym.kernel
  have hm := hR.integrable (nsp β)
  set f : ℝ → ℝ × ℝ × ℝ → ℂ := fun s γ => R.m (nsp β) γ * (chiInvR (raR R β + γ.2.2) : ℂ) *
    (jker (rbR R β) γ.1 γ.2.1 t s * expF lam s) with hf
  have e1 : ∀ s, (∫ γ : ℝ × ℝ × ℝ, R.m (nsp β) γ * rker (bundle R.y₁ (nsp β) + R.ε * β none)
      (bundle R.y₂ (nsp β) + R.ε * β none) γ.1 γ.2.1 γ.2.2 t s) * expF lam s = ∫ γ, f s γ := by
    intro s
    rw [← MeasureTheory.integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
    simp only [hf, rker, raR, rbR]
    ring
  simp_rw [e1]
  rw [intervalIntegral_integral_swap]
  · refine integral_congr_ae (Eventually.of_forall fun γ => ?_)
    simp only [hf]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    simp_rw [jker_mul_expF]
    rw [intervalIntegral.integral_const_mul]
    unfold eInt
    push_cast
    rfl
  · -- integrability on `(0, t] × ℝ³`
    have : IsFiniteMeasure (volume.restrict (uIoc 0 t)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    have hg : Integrable (fun p : ℝ × (ℝ × ℝ × ℝ) => (1 : ℝ) * (CPhi * ‖R.m (nsp β) p.2‖))
        ((volume.restrict (uIoc 0 t)).prod volume) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) (hm.norm.const_mul CPhi)
    refine Integrable.mono' hg ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : StronglyMeasurable fun p : ℝ × (ℝ × ℝ × ℝ) => R.m (nsp β) p.2 :=
        (hR.meas.comp_measurable (measurable_const.prodMk measurable_id)).comp_measurable
          measurable_snd
      have h2 : Continuous fun p : ℝ × (ℝ × ℝ × ℝ) => (chiInvR (raR R β + p.2.2.2) : ℂ) *
          (jker (rbR R β) p.2.1 p.2.2.1 t p.1 * expF lam p.1) := by
        have hc : Continuous chiInvR := contDiff_chiInvR.continuous
        unfold jker expF; fun_prop
      have := (h1.mul h2.stronglyMeasurable).aestronglyMeasurable
        (μ := (volume.restrict (uIoc 0 t)).prod volume)
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp only [hf, Function.uncurry, Pi.mul_apply]; ring
    · simp only [Function.uncurry, hf, one_mul]
      rw [norm_mul, norm_mul, norm_mul, norm_jker, norm_expF, mul_one, mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_right ((norm_chiInvR_le _)) (norm_nonneg _)

theorem lintegral_decay_pair_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (c₁ c₂ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |c₁ + ε * x|)⁻¹ * (1 + |c₂ - ε * x|)⁻¹) ≤ ENNReal.ofReal π := by
  rcases hε with rfl | rfl
  · refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (lintegral_decay_pair (-c₁) c₂)
    congr 3
    · rw [show c₁ + ((1 : ℤ) : ℝ) * x = x - -c₁ by push_cast; ring]
    · rw [show c₂ - ((1 : ℤ) : ℝ) * x = -(x - c₂) by push_cast; ring, abs_neg]
  · refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (lintegral_decay_pair c₁ (-c₂))
    congr 3
    · rw [show c₁ + ((-1 : ℤ) : ℝ) * x = -(x - c₁) by push_cast; ring, abs_neg]
    · rw [show c₂ - ((-1 : ℤ) : ℝ) * x = x - -c₂ by push_cast; ring]

theorem integrable_norm_mul_D (R : RSym ι) (hR : SymReg R.m) (β : Option ι → ℝ) (lam : ℝ) :
    Integrable fun γ : ℝ × ℝ × ℝ => ‖R.m (nsp β) γ‖ * (2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ *
      (1 + |γ.2.1 + lam - rbR R β|)⁻¹)) := by
  refine ((hR.integrable (nsp β)).norm.mul_const (2 * CPhi)).mono' ?_ ?_
  · have h1 : StronglyMeasurable fun γ : ℝ × ℝ × ℝ => ‖R.m (nsp β) γ‖ :=
      (hR.meas.comp_measurable (measurable_const.prodMk measurable_id)).norm
    have h2 : Continuous fun γ : ℝ × ℝ × ℝ => 2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ *
        (1 + |γ.2.1 + lam - rbR R β|)⁻¹) := by
      refine continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun γ => by positivity).mul
        (Continuous.inv₀ (by fun_prop) fun γ => by positivity))
    exact (h1.mul h2.stronglyMeasurable).aestronglyMeasurable
  · refine Eventually.of_forall fun γ => ?_
    have hC := CPhi_nonneg
    have i1 : (1 + |raR R β + γ.2.2|)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [abs_nonneg (raR R β + γ.2.2)])
    have i2 : (1 + |γ.2.1 + lam - rbR R β|)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [abs_nonneg (γ.2.1 + lam - rbR R β)])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc 2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ * (1 + |γ.2.1 + lam - rbR R β|)⁻¹)
        ≤ 2 * CPhi * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul i1 i2 (by positivity) zero_le_one) (by positivity)
      _ = 2 * CPhi := by ring

theorem norm_volterra_RSym_le (R : RSym ι) (hR : SymReg R.m) (β : Option ι → ℝ) (lam : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖volterra (R.kernel β) (expF lam) t‖ ≤ ∫ γ : ℝ × ℝ × ℝ, ‖R.m (nsp β) γ‖ *
      (2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ * (1 + |γ.2.1 + lam - rbR R β|)⁻¹)) := by
  rw [volterra_RSym_exp R hR β lam t]
  have hc : Continuous chiInvR := contDiff_chiInvR.continuous
  have hpt : ∀ γ : ℝ × ℝ × ℝ, ‖R.m (nsp β) γ * (chiInvR (raR R β + γ.2.2) : ℂ) *
      (cexp (π * I * ((rbR R β + γ.1) * t)) * eInt (γ.2.1 + lam - rbR R β) t)‖ ≤
      ‖R.m (nsp β) γ‖ * (2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ *
        (1 + |γ.2.1 + lam - rbR R β|)⁻¹)) := by
    intro γ
    have h1 := norm_chiInvR_mul_le (raR R β + γ.2.2)
    have h2 := norm_eInt_mul_le (x := γ.2.1 + lam - rbR R β) ht
    have p1 : 0 < 1 + |raR R β + γ.2.2| := by positivity
    have p2 : 0 < 1 + |γ.2.1 + lam - rbR R β| := by positivity
    rw [norm_mul, norm_mul, norm_mul,
      show cexp (π * I * ((((rbR R β : ℝ) : ℂ) + (γ.1 : ℂ)) * (t : ℂ))) =
        cexp (π * I * (((rbR R β + γ.1) * t : ℝ) : ℂ)) by push_cast; ring_nf,
      norm_cexp_piI, one_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← le_div_iff₀ p1] at h1
    rw [← le_div_iff₀ p2] at h2
    calc ‖(chiInvR (raR R β + γ.2.2) : ℂ)‖ * ‖eInt (γ.2.1 + lam - rbR R β) t‖
        ≤ (CPhi / (1 + |raR R β + γ.2.2|)) * (2 / (1 + |γ.2.1 + lam - rbR R β|)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by have := CPhi_nonneg; positivity)
      _ = 2 * CPhi * ((1 + |raR R β + γ.2.2|)⁻¹ * (1 + |γ.2.1 + lam - rbR R β|)⁻¹) := by
          field_simp
  exact (MeasureTheory.norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (integrable_norm_mul_D R hR β lam)
    (Eventually.of_forall hpt))

theorem rsym_lintegral_le {R : RSym ι} {θ A N : ℝ} (hR : R.Bound θ A N) (hθ : 0 ≤ θ) :
    ∫⁻ β, ∫⁻ γ, ‖R.m β γ‖ₑ ≤ ENNReal.ofReal N := by
  have h := hR.norm 0
  unfold rNorm gev at h
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one] at h
  refine le_trans (lintegral_mono fun β => lintegral_mono fun γ => ?_) h
  rw [dnorm_zero]
  exact le_mul_of_one_le_left bot_le (one_le_wR hθ β γ.1 γ.2.2)

theorem stronglyMeasurable_RSym_kernel (R : RSym ι) (hR : SymReg R.m) (t : ℝ) :
    StronglyMeasurable fun p : (Option ι → ℝ) × ℝ => R.kernel p.1 t p.2 := by
  unfold RSym.kernel
  have hnsp : Measurable fun q : ((Option ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => nsp q.1.1 := by
    unfold nsp; fun_prop
  have hm : StronglyMeasurable fun q : ((Option ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => R.m (nsp q.1.1) q.2 :=
    hR.meas.comp_measurable (hnsp.prodMk measurable_snd)
  have hc : Continuous chiInvR := contDiff_chiInvR.continuous
  have hr : StronglyMeasurable fun q : ((Option ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) =>
      rker (bundle R.y₁ (nsp q.1.1) + R.ε * q.1.1 none) (bundle R.y₂ (nsp q.1.1) + R.ε * q.1.1 none)
        q.2.1 q.2.2.1 q.2.2.2 t q.1.2 := by
    refine Continuous.stronglyMeasurable ?_
    have h1 := continuous_bundle R.y₁
    have h2 := continuous_bundle R.y₂
    have hn : Continuous fun q : ((Option ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => nsp q.1.1 := by
      unfold nsp; fun_prop
    unfold rker jker
    fun_prop
  exact (hm.mul hr).integral_prod_right'

/-- **A basic class `R` operator applied to `e^{πiλs}` is integrable in its variables.** -/
theorem integrable_volterra_RSym {R : RSym ι} {θ A N : ℝ} (hR : R.Bound θ A N) (hθ : 0 ≤ θ)
    (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable fun β : Option ι → ℝ => volterra (R.kernel β) (expF lam) t := by
  have hmeas := stronglyMeasurable_volterra (stronglyMeasurable_RSym_kernel R hR.reg t)
    (expF lam) (continuous_expF lam)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  set D : (Option ι → ℝ) → ℝ × ℝ × ℝ → ℝ := fun β γ => 2 * CPhi *
    ((1 + |raR R β + γ.2.2|)⁻¹ * (1 + |γ.2.1 + lam - rbR R β|)⁻¹) with hD
  have hDn : ∀ β γ, 0 ≤ D β γ := fun β γ => by have := CPhi_nonneg; simp only [hD]; positivity
  -- pointwise
  have h1 : ∀ β, ‖volterra (R.kernel β) (expF lam) t‖ₑ ≤
      ∫⁻ γ, ‖R.m (nsp β) γ‖ₑ * ENNReal.ofReal (D β γ) := by
    intro β
    have hb := norm_volterra_RSym_le R hR.reg β lam ht
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hb).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_mono fun γ => ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    · exact integrable_norm_mul_D R hR.reg β lam
    · exact Eventually.of_forall fun γ => mul_nonneg (norm_nonneg _) (hDn β γ)
  -- the change of variables `β = (β[ι], β none)`
  set e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)
  have hp : MeasurePreserving e.symm ((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod volume)
      (Measure.pi fun _ : Option ι => (volume : Measure ℝ)) :=
    ⟨e.symm.measurable, Measure.pi_map_piOptionEquivProd (β := fun _ : Option ι => ℝ)
      (fun _ => (volume : Measure ℝ))⟩
  have hnsp : ∀ (x : ι → ℝ) (y : ℝ), nsp (e.symm (x, y)) = x := fun x y => rfl
  have hnone : ∀ (x : ι → ℝ) (y : ℝ), e.symm (x, y) none = y := fun x y => rfl
  have hmR := hR.reg.meas
  have hGm : Measurable fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) =>
      ‖R.m q.1.1 q.2‖ₑ * ENNReal.ofReal (D (e.symm q.1) q.2) := by
    have hm1 : Measurable fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => ‖R.m q.1.1 q.2‖ₑ :=
      (hmR.comp_measurable (measurable_fst.fst.prodMk measurable_snd)).measurable.enorm
    have hD1 : Measurable fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => D (e.symm q.1) q.2 := by
      have hc : Continuous fun q : ((ι → ℝ) × ℝ) × (ℝ × ℝ × ℝ) => D (e.symm q.1) q.2 := by
        simp only [hD, raR, rbR, hnsp, hnone]
        have h1 := continuous_bundle R.y₁
        have h2 := continuous_bundle R.y₂
        refine continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun q => by positivity).mul
          (Continuous.inv₀ (by fun_prop) fun q => by positivity))
      exact hc.measurable
    exact hm1.mul hD1.ennreal_ofReal
  have hc2 : 0 ≤ 2 * CPhi := by have := CPhi_nonneg; positivity
  calc ∫⁻ β, ‖volterra (R.kernel β) (expF lam) t‖ₑ
      ≤ ∫⁻ β, ∫⁻ γ, ‖R.m (nsp β) γ‖ₑ * ENNReal.ofReal (D β γ) := lintegral_mono h1
    _ = ∫⁻ q, (∫⁻ γ : ℝ × ℝ × ℝ, ‖R.m q.1 γ‖ₑ * ENNReal.ofReal (D (e.symm q) γ))
          ∂((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod volume) := by
        exact (hp.lintegral_comp_emb e.symm.measurableEmbedding
          (fun β => ∫⁻ γ, ‖R.m (nsp β) γ‖ₑ * ENNReal.ofReal (D β γ))).symm
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ γ, ‖R.m x γ‖ₑ * ENNReal.ofReal (D (e.symm (x, y)) γ) :=
        lintegral_prod _ hGm.lintegral_prod_right'.aemeasurable
    _ = ∫⁻ x, ∫⁻ γ, ∫⁻ y, ‖R.m x γ‖ₑ * ENNReal.ofReal (D (e.symm (x, y)) γ) := by
        refine lintegral_congr fun x => lintegral_lintegral_swap ?_
        exact (hGm.comp (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd)).aemeasurable
    _ ≤ ∫⁻ x, ∫⁻ γ, ‖R.m x γ‖ₑ * (ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal π) := by
        refine lintegral_mono fun x => lintegral_mono fun γ => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        gcongr
        simp only [hD, raR, rbR, hnsp, hnone]
        calc ∫⁻ y, ENNReal.ofReal (2 * CPhi * ((1 + |bundle R.y₁ x + R.ε * y + γ.2.2|)⁻¹ *
              (1 + |γ.2.1 + lam - (bundle R.y₂ x + R.ε * y)|)⁻¹))
            = ∫⁻ y, ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal
                ((1 + |(bundle R.y₁ x + γ.2.2) + R.ε * y|)⁻¹ *
                  (1 + |(γ.2.1 + lam - bundle R.y₂ x) - R.ε * y|)⁻¹) := by
              refine lintegral_congr fun y => ?_
              rw [← ENNReal.ofReal_mul hc2]
              congr 4 <;> ring_nf
          _ ≤ ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal π := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              gcongr
              exact lintegral_decay_pair_sign hR.sign _ _
    _ = ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal π * ∫⁻ x, ∫⁻ γ, ‖R.m x γ‖ₑ := by
        have hne : ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal π ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        rw [← lintegral_const_mul' _ _ hne]
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul' _ _ hne]
        refine lintegral_congr fun γ => ?_
        ring
    _ ≤ ENNReal.ofReal (2 * CPhi) * ENNReal.ofReal π * ENNReal.ofReal N := by
        gcongr; exact rsym_lintegral_le hR hθ
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top

end Basic

/-! ### Masked operators -/

section Masked

variable {V : Type} [DecidableEq V]

/-- The equivalence `ι ≃ W` of an injection with range `W`. -/
@[expose] noncomputable def eqvOfRange {ι : Type*} {W : Finset V} (f : ι → V)
    (hf : Function.Injective f) (hr : Set.range f = ↑W) : ι ≃ ↥W :=
  Equiv.ofBijective (fun i => ⟨f i, by rw [← Finset.mem_coe, ← hr]; exact ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf (congrArg Subtype.val h), fun w => by
      obtain ⟨i, hi⟩ : w.1 ∈ Set.range f := by rw [hr]; exact w.2
      exact ⟨i, Subtype.ext hi⟩⟩

omit [DecidableEq V] in
theorem eqvOfRange_apply {ι : Type*} {W : Finset V} (f : ι → V) (hf : Function.Injective f)
    (hr : Set.range f = ↑W) (i : ι) : (eqvOfRange f hf hr i : V) = f i := rfl

/-- **Transport of integrability to `α[W]`** along an injection with range `W`. -/
theorem mInt_of_integrable_comp {ι : Type} [Fintype ι] {W : Finset V} {f : ι → V}
    (hf : Function.Injective f) (hr : Set.range f = ↑W) {G : (ι → ℝ) → ℂ} (hG : Integrable G)
    (α₀ : V → ℝ) : MInt W (fun α => G (α ∘ f)) α₀ := by
  set e := eqvOfRange f hf hr
  have hp := measurePreserving_piCongrLeft (fun _ : ↥W => (volume : Measure ℝ)) e
  have h2 := (hp.symm (MeasurableEquiv.piCongrLeft (fun _ : ↥W => ℝ) e)).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : ↥W => ℝ) e).symm.measurableEmbedding (g := G)
  unfold MInt
  refine (h2.2 hG).congr (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  congr 1
  funext i
  have hi : f i ∈ W := by rw [← Finset.mem_coe, ← hr]; exact ⟨i, rfl⟩
  rw [Function.comp_apply, Function.updateFinset_def]
  simp only [hi, dite_true]
  have : (⟨f i, hi⟩ : ↥W) = e i := rfl
  rw [this]
  rw [MeasurableEquiv.coe_piCongrLeft] at *
  rfl

/-- The volterra of a finite sum of kernels with bounded measurable sections. -/
theorem volterra_sum {n : ℕ} (K : Fin n → ℝ → ℝ → ℂ) {t : ℝ} (lam : ℝ)
    (hK : ∀ i, IntervalIntegrable (fun s => K i t s * expF lam s) volume 0 t) :
    volterra (fun t s => ∑ i, K i t s) (expF lam) t = ∑ i, volterra (K i) (expF lam) t := by
  unfold volterra
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i _ => hK i

theorem volterra_congr_tri {K L : ℝ → ℝ → ℂ} (h : KEqOn K L) (g : ℝ → ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : volterra K g t = volterra L g t := by
  unfold volterra
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  rw [h t s hs.1 hs.2 ht.2]

theorem intervalIntegrable_of_sm {X : Type*} [MeasurableSpace X] {K : X → ℝ → ℝ → ℂ} {t : ℝ}
    (hK : StronglyMeasurable fun p : X × ℝ => K p.1 t p.2) (x : X) {C : ℝ}
    (hb : ∀ s, ‖K x t s‖ ≤ C) (lam : ℝ) :
    IntervalIntegrable (fun s => K x t s * expF lam s) volume 0 t := by
  have hm : StronglyMeasurable fun s => K x t s * expF lam s :=
    (hK.comp_measurable (measurable_const.prodMk measurable_id)).mul
      (continuous_expF lam).stronglyMeasurable
  refine (intervalIntegrable_const (c := C)).mono_fun' hm.aestronglyMeasurable ?_
  refine Eventually.of_forall fun s => ?_
  show ‖K x t s * expF lam s‖ ≤ C
  rw [norm_mul, norm_expF, mul_one]
  exact hb s

theorem intervalIntegrable_sum_mul {κ : Type*} [Fintype κ] (K : κ → ℝ → ℂ) (g : ℝ → ℂ) {a b : ℝ}
    (h : ∀ i, IntervalIntegrable (fun s => K i s * g s) volume a b) :
    IntervalIntegrable (fun s => (∑ i, K i s) * g s) volume a b := by
  refine (IntervalIntegrable.sum Finset.univ fun i _ => h i).congr fun s _ => ?_
  simp [Finset.sum_apply, Finset.sum_mul]

theorem norm_RSym_kernel_le {ι : Type*} [Fintype ι] (R : RSym ι) (hR : SymReg R.m)
    (β : Option ι → ℝ) (t s : ℝ) :
    ‖R.kernel β t s‖ ≤ CPhi * ∫ γ, ‖R.m (nsp β) γ‖ := by
  unfold RSym.kernel
  rw [← MeasureTheory.integral_const_mul]
  have hi : Integrable (fun γ : ℝ × ℝ × ℝ => CPhi * ‖R.m (nsp β) γ‖) :=
    (SymReg.integrable hR (nsp β)).norm.const_mul CPhi
  refine MeasureTheory.norm_integral_le_of_norm_le hi (Eventually.of_forall fun γ => ?_)
  rw [norm_mul, rker, norm_mul, norm_jker, mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_chiInvR_le _) (norm_nonneg _)

variable {P : Type*} [MeasurableSpace P] {θ A N : ℝ}

omit [DecidableEq V] in
theorem mJ_intervalIntegrable {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MJ θ A N S T)
    (p : P) (α : V → ℝ) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => T p α t s * expF lam s) volume 0 t := by
  obtain ⟨ι, _, f, hf, hr, T', ⟨n, R, c, hb, -, he'⟩, he⟩ := h
  have hsum : IntervalIntegrable (fun s => (∑ i, ((R i).get p).kernel (α ∘ f) t s) * expF lam s)
      volume 0 t :=
    intervalIntegrable_sum_mul _ _ fun i => intervalIntegrable_of_sm
      (stronglyMeasurable_JSym_kernel _ ((hb i).bound p).reg t) (α ∘ f)
      (fun s => norm_JSym_kernel_le _ (α ∘ f) t s) lam
  refine hsum.congr fun s hs => ?_
  rw [uIoc_of_le ht.1] at hs
  show (∑ i, ((R i).get p).kernel (α ∘ f) t s) * expF lam s = T p α t s * expF lam s
  rw [((he p α).trans (he' p (α ∘ f))) t s hs.1.le hs.2 ht.2]

omit [DecidableEq V] in
theorem mR0_intervalIntegrable {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MR0 θ A N S T)
    (p : P) (α : V → ℝ) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => T p α t s * expF lam s) volume 0 t := by
  rcases h with ⟨v₀, ι, _, f, hf, hr, -, T', ⟨n, R, c, hb, -, he'⟩, he⟩ | ⟨-, hz⟩
  · have hsum : IntervalIntegrable (fun s => (∑ i, ((R i).get p).kernel (α ∘ f) t s) * expF lam s)
        volume 0 t :=
      intervalIntegrable_sum_mul _ _ fun i => intervalIntegrable_of_sm
        (stronglyMeasurable_RSym_kernel _ ((hb i).bound p).reg t) (α ∘ f)
        (fun s => norm_RSym_kernel_le _ ((hb i).bound p).reg (α ∘ f) t s) lam
    refine hsum.congr fun s hs => ?_
    rw [uIoc_of_le ht.1] at hs
    show (∑ i, ((R i).get p).kernel (α ∘ f) t s) * expF lam s = T p α t s * expF lam s
    rw [((he p α).trans (he' p (α ∘ f))) t s hs.1.le hs.2 ht.2]
  · refine (intervalIntegrable_const (c := (0 : ℂ))).congr fun s hs => ?_
    rw [uIoc_of_le ht.1] at hs
    show (0 : ℂ) = T p α t s * expF lam s
    rw [hz p α t s hs.1.le hs.2 ht.2, zero_mul]

/-- **A masked class `J` operator applied to `e^{πiλs}` is integrable over `α[W]`.** -/
theorem mJ_mInt_volterra {W : Finset V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MJ θ A N ↑W T)
    (hθ : 0 ≤ θ) (p : P) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    MInt W (fun α => volterra (T p α) (expF lam) t) α₀ := by
  obtain ⟨ι, _, f, hf, hr, T', ⟨n, R, c, hb, -, he'⟩, he⟩ := h
  have e1 : ∀ α, volterra (T p α) (expF lam) t =
      ∑ i, volterra (((R i).get p).kernel (α ∘ f)) (expF lam) t := by
    intro α
    rw [volterra_congr_tri ((he p α).trans (he' p (α ∘ f))) _ ht, volterra_sum _ lam]
    intro i
    exact intervalIntegrable_of_sm (stronglyMeasurable_JSym_kernel _ ((hb i).bound p).reg t) _
      (fun s => norm_JSym_kernel_le _ _ t s) lam
  unfold MInt
  simp_rw [e1]
  refine integrable_finsetSum _ fun i _ => ?_
  exact mInt_of_integrable_comp hf hr (G := fun β => volterra (((R i).get p).kernel β) (expF lam) t)
    (integrable_volterra_JSym ((hb i).bound p) hθ lam ht) α₀

/-- **A masked class `R` operator applied to `e^{πiλs}` is integrable over `α[W]`.** -/
theorem mR0_mInt_volterra {W : Finset V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MR0 θ A N ↑W T)
    (hθ : 0 ≤ θ) (p : P) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    MInt W (fun α => volterra (T p α) (expF lam) t) α₀ := by
  rcases h with ⟨v₀, ι, _, f, hf, hr, -, T', ⟨n, R, c, hb, -, he'⟩, he⟩ | ⟨-, hz⟩
  · have e1 : ∀ α, volterra (T p α) (expF lam) t =
        ∑ i, volterra (((R i).get p).kernel (α ∘ f)) (expF lam) t := by
      intro α
      rw [volterra_congr_tri ((he p α).trans (he' p (α ∘ f))) _ ht, volterra_sum _ lam]
      intro i
      exact intervalIntegrable_of_sm (stronglyMeasurable_RSym_kernel _ ((hb i).bound p).reg t) _
        (fun s => norm_RSym_kernel_le _ ((hb i).bound p).reg _ t s) lam
    unfold MInt
    simp_rw [e1]
    refine integrable_finsetSum _ fun i _ => ?_
    exact mInt_of_integrable_comp hf hr
      (G := fun β => volterra (((R i).get p).kernel β) (expF lam) t)
      (integrable_volterra_RSym ((hb i).bound p) hθ lam ht) α₀
  · have e1 : ∀ α, volterra (T p α) (expF lam) t = 0 := by
      intro α
      rw [volterra_congr_tri (hz p α) _ ht]
      simp [volterra]
    unfold MInt
    simp_rw [e1]
    exact integrable_zero _ _ _

/-- **DH21 (L1720): a class `J` plus class `R` operator in the variables `W`, applied to `e^{πiλs}`, is
integrable over `α[W]`.** -/
theorem mJR_mInt_volterra {W : Finset V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MJR θ A N ↑W T)
    (hθ : 0 ≤ θ) (p : P) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    MInt W (fun α => volterra (T p α) (expF lam) t) α₀ := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, -, he⟩ := h
  have hJ' := mJ_mInt_volterra hJ hθ p lam ht α₀
  have hR' := mR0_mInt_volterra hR hθ p lam ht α₀
  have e1 : ∀ α, volterra (T p α) (expF lam) t =
      volterra (TJ p α) (expF lam) t + volterra (TR p α) (expF lam) t := by
    intro α
    rw [volterra_congr_tri (he p α) _ ht]
    unfold volterra
    simp_rw [add_mul]
    exact intervalIntegral.integral_add (mJ_intervalIntegrable hJ p α lam ht)
      (mR0_intervalIntegrable hR p α lam ht)
  unfold MInt at hJ' hR' ⊢
  simp_rw [e1]
  exact hJ'.add hR'

end Masked

end WaveTurbulence.Cancel

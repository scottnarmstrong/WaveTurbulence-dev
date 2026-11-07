/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeBound
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import WaveTurbulence.Foundations.XChain.JbrBounds
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (b): difference-quotient weights lose exactly one derivative

TARGET Prop `vineest` Step 4, (replaceterm1), clause (b): the factor
`(𝒦_𝒬)_app(·,·,y_*) - (𝒦_𝒬)_app(·,·,x_*)` with `x_* - y_* = ±r` is bounded by `|r|` and leads to
assumption (b) of `sumint` (weight `(f(k+a) - f(k))/|a|` times the other factors, with `|a| = |r|`).
Here `f ∈ 𝔖^{A+1,K}` gives `(f(k+a) - f(k))/|a| ∈ 𝔖^{A,K}` for `|a| ≤ 1`: the derivative loss
(finding F1) is exactly one derivative, absorbed by the weight regularity `wN` of `SumintPar`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset WaveTurbulence.LGSpine

namespace WaveTurbulence.VineEstS4c

variable {d : ℕ}

/-- `jbr` is `1`-Lipschitz. -/
theorem jbr_le_jbr_add_norm (x y : Mom d) : jbr x ≤ jbr y + ‖x - y‖ := by
  have hy : ‖y‖ ≤ jbr y := by
    unfold jbr
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖y‖])
  have hxy : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have := norm_le_norm_add_norm_sub' x y
    linarith [norm_sub_rev x y]
  have hs := norm_nonneg (x - y)
  have h1 : 0 ≤ ‖y‖ := norm_nonneg y
  have hjy : 0 ≤ jbr y := (jbr_pos y).le
  unfold jbr at *
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hy2 : (Real.sqrt (1 + ‖y‖ ^ 2)) ^ 2 = 1 + ‖y‖ ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hy hs, mul_nonneg h1 hs, sq_nonneg (‖x‖ - ‖y‖ - ‖x - y‖),
    mul_self_le_mul_self (norm_nonneg x) hxy]

/-- Peetre for unit shifts. -/
theorem jbr_le_two_mul_jbr_add (x b : Mom d) (hb : ‖b‖ ≤ 1) : jbr x ≤ 2 * jbr (x + b) := by
  have h := jbr_le_jbr_add_norm x (x + b)
  have h2 : ‖x - (x + b)‖ ≤ 1 := by simpa using hb
  have := one_le_jbr (x + b)
  linarith

theorem contDiff_of_SNorm_le' {A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℂ) (C : ℝ)
    (h : SNorm A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  have ht : SNorm A B f < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  unfold SNorm at ht
  split_ifs at ht with hf
  · exact hf.resolve_left hA
  · exact absurd ht (by simp)

theorem norm_momentumDerivative_le_frechet' {n : ℕ} (f : Mom d → ℂ)
    (ρ : Fin n → Fin d) (x : Mom d) :
    ‖Fourier.momentumDerivative ρ f x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  unfold Fourier.momentumDerivative
  have h := (iteratedFDeriv ℝ n f x).le_opNorm (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))
  simpa using h

/-- A weighted bound on the Fréchet derivatives gives the `𝔖`-norm bound. -/
theorem SNorm_le_of_frechet_bounds {A B : ℕ} (g : Mom d → ℂ) (hg : ContDiff ℝ A g) (C : ℝ)
    (h : ∀ n ≤ A, ∀ x, jbr x ^ B * ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    SNorm A B g ≤ ENNReal.ofReal C := by
  apply SNorm_le_of_momentum_bounds g hg
  intro n hn ρ x
  exact (mul_le_mul_of_nonneg_left (norm_momentumDerivative_le_frechet' g ρ x)
    (pow_nonneg (jbr_pos x).le B)).trans (h n hn x)

/-- Mean value bound for the `n`-th derivative of a translation difference. -/
theorem norm_iteratedFDeriv_shiftDiff_le {n : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ (n + 1) f)
    (a x : Mom d) (C : ℝ)
    (hC : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖iteratedFDeriv ℝ (n + 1) f (x + s • a)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun k => f (k + a) - f k) x‖ ≤ C * ‖a‖ := by
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hfa : ContDiff ℝ (n + 1) (fun k => f (k + a)) := hf.comp (contDiff_id.add contDiff_const)
  have h1 : iteratedFDeriv ℝ n (fun k => f (k + a) - f k) x =
      iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    show iteratedFDeriv ℝ n ((fun k => f (k + a)) - f) x = _
    rw [iteratedFDeriv_sub_apply (hfa.contDiffAt.of_le hn) (hf.contDiffAt.of_le hn),
      iteratedFDeriv_comp_add_right]
  rw [h1]
  have hdiff : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ n f) z := fun z =>
    hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n) z
  have hmv := (convex_segment x (x + a)).norm_image_sub_le_of_norm_fderiv_le
    (f := iteratedFDeriv ℝ n f) (C := C) (fun z _ => hdiff z)
    (fun z hz => by
      rw [segment_eq_image'] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      rw [norm_fderiv_iteratedFDeriv]
      have h := hC s hs
      simpa using h)
    (left_mem_segment ℝ x (x + a)) (right_mem_segment ℝ x (x + a))
  simpa using hmv

/-- The normalized difference quotient `(f(k+a) - f(k))/|a|`. -/
@[expose] noncomputable def diffQuot (a : Mom d) (f : Mom d → ℂ) : Mom d → ℂ :=
  fun k => ((‖a‖ : ℝ) : ℂ)⁻¹ * (f (k + a) - f k)

/-- **Clause (b): one derivative is lost, no more.** -/
theorem SNorm_diffQuot_le {A K : ℕ} {f : Mom d → ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hf : SNorm (A + 1) K f ≤ ENNReal.ofReal β) (a : Mom d) (ha : ‖a‖ ≤ 1) :
    SNorm A K (diffQuot a f) ≤ ENNReal.ofReal ((2 : ℝ) ^ K * (d : ℝ) ^ (A + 1) * β) := by
  have hfc : ContDiff ℝ (A + 1) f := contDiff_of_SNorm_le' (Nat.succ_ne_zero A) f β hf
  have hdq : ContDiff ℝ A (diffQuot a f) := by
    unfold diffQuot
    exact contDiff_const.mul (((hfc.of_le (by exact_mod_cast Nat.le_succ A)).comp
      (contDiff_id.add contDiff_const)).sub (hfc.of_le (by exact_mod_cast Nat.le_succ A)))
  apply SNorm_le_of_frechet_bounds _ hdq
  intro n hn x
  have hn1 : n + 1 ≤ A + 1 := by omega
  have hbound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖iteratedFDeriv ℝ (n + 1) f (x + s • a)‖ ≤
      (2 : ℝ) ^ K * (d : ℝ) ^ (n + 1) * β / jbr x ^ K := by
    intro s hs
    have hy : ‖s • a‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖a‖ ≤ 1 * 1 := mul_le_mul hs.2 ha (norm_nonneg a) zero_le_one
        _ = 1 := one_mul 1
    have hp := SNorm_frechet_pointwise f hfc β hβ hf hn1 (x + s • a)
    have hj := jbr_le_two_mul_jbr_add x (s • a) hy
    have hjy : 0 < jbr (x + s • a) := jbr_pos _
    have hjx : 0 < jbr x := jbr_pos x
    rw [le_div_iff₀ (pow_pos hjx K)]
    calc ‖iteratedFDeriv ℝ (n + 1) f (x + s • a)‖ * jbr x ^ K
        ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + s • a)‖ * (2 * jbr (x + s • a)) ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hjx.le hj K) (norm_nonneg _)
      _ = 2 ^ K * (jbr (x + s • a) ^ K * ‖iteratedFDeriv ℝ (n + 1) f (x + s • a)‖) := by
          rw [mul_pow]; ring
      _ ≤ 2 ^ K * ((d : ℝ) ^ (n + 1) * β) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hmv := norm_iteratedFDeriv_shiftDiff_le (n := n) (hfc.of_le (by exact_mod_cast hn1)) a x _ hbound
  have hnorm : ‖iteratedFDeriv ℝ n (diffQuot a f) x‖ ≤
      ‖a‖⁻¹ * ‖iteratedFDeriv ℝ n (fun k => f (k + a) - f k) x‖ := by
    have hsm : diffQuot a f = ((‖a‖ : ℝ) : ℂ)⁻¹ • (fun k => f (k + a) - f k) := by
      funext k; simp [diffQuot]
    rw [hsm]
    have hnA : ((n : ℕ) : WithTop ℕ∞) ≤ (A + 1 : ℕ) := by exact_mod_cast (show n ≤ A + 1 by omega)
    have hc : ContDiffAt ℝ n (fun k => f (k + a) - f k) x :=
      (((hfc.of_le hnA).comp (contDiff_id.add contDiff_const)).sub (hfc.of_le hnA)).contDiffAt
    rw [show (((‖a‖ : ℝ) : ℂ)⁻¹ • (fun k => f (k + a) - f k)) = fun k => ((‖a‖ : ℝ) : ℂ)⁻¹ • (f (k + a) - f k) from rfl,
      iteratedFDeriv_const_smul_apply' hc, norm_smul, norm_inv, Complex.norm_real, norm_norm]
  have hjx : 0 < jbr x := jbr_pos x
  have hinv : ‖a‖⁻¹ * ‖a‖ ≤ 1 := by
    by_cases h0 : ‖a‖ = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  have hd : (1 : ℝ) ≤ d ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact Or.inr h
    · exact Or.inl (by exact_mod_cast h)
  set C' : ℝ := (2 : ℝ) ^ K * (d : ℝ) ^ (n + 1) * β with hC'
  have hC'0 : 0 ≤ C' := by positivity
  calc jbr x ^ K * ‖iteratedFDeriv ℝ n (diffQuot a f) x‖
      ≤ jbr x ^ K * (‖a‖⁻¹ * (C' / jbr x ^ K * ‖a‖)) :=
        mul_le_mul_of_nonneg_left (hnorm.trans (mul_le_mul_of_nonneg_left hmv (by positivity)))
          (by positivity)
    _ = C' * (‖a‖⁻¹ * ‖a‖) := by field_simp
    _ ≤ C' * 1 := mul_le_mul_of_nonneg_left hinv hC'0
    _ ≤ _ := by
        rw [mul_one]
        rcases hd with hd | hd
        · have hp : (d : ℝ) ^ (n + 1) ≤ (d : ℝ) ^ (A + 1) := pow_le_pow_right₀ hd (by omega)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hβ
        · subst hd; simp [hC']

end WaveTurbulence.VineEstS4c

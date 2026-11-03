/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Bump
public import WaveTurbulence.Foundations.ClassJR.Convert
public import WaveTurbulence.Foundations.Fourier.Chi0Gevrey

/-!
# The fixed functions of the class `J`/`R` calculus

DH21 §5.2 splits `∫_0^v e^{πixu} du` with `1 = χ₀(x) + χ_∞(x)` (proof of Lemma 5.3, L976–L978):

* the `χ_∞` part is `Φ(x) (e^{πixv} - 1)` with `Φ(x) = χ_∞(x)/(πix)` (`chiInfinity_mul_eInt`), and
  `chiInvR x = χ_∞(x)/x` is smooth with `(1 + |x|) |∂^c chiInvR(x)| ≤ C A^c (2c)!`
  (`chiInvR_gevrey`);
* the `χ₀` part is a superposition `∫∫ kerM(x; σ, τ) e^{πiσv} dσ dτ` for `v ∈ [0, 1]`
  (`integral_kerM_mul_exp`), where `kerM(x; σ, τ) = χ₀(x) ftπ φ(σ - τx) 1_{[0,1]}(τ)` and
  `φ(v) = v χ₀(v - 1/2)`. This is DH21's "fixed decaying Gevrey 2 function `M`" (L978), written
  with an extra variable `τ` so that its `x`-derivatives are explicit:
  `|∂_x^c kerM(x; σ, τ)| ≤ 1_{[0,1]}(τ) C A^c (2c)! (1 + |σ|)^{-3}` (`exists_kerM_bound`);
* the function `M₀ = ftπ (χ₀(· - 1/2))` of DH21 (extraid) (L1037):
  `e^{πiμs} = ∫ M₀(σ) e^{πi(μ+σ)s} dσ` for `s ∈ [0, 1]` (`integral_M0_mul_exp`).
-/

public section

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

/-- The Gevrey radius of the fixed cutoff (`Chi0Gevrey.lean`). -/
@[expose] noncomputable def Achi : ℝ := 16 + 16 * Real.exp 2

theorem two_le_Achi : 2 ≤ Achi := by
  unfold Achi; nlinarith [Real.exp_pos 2]

theorem Achi_nonneg : 0 ≤ Achi := by linarith [two_le_Achi]

section Real

/-- Real-valued smooth functions have the same derivative norms as their complex lifts. -/
theorem norm_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℕ) (x : ℝ) :
    ‖iteratedDeriv c (fun y => (f y : ℂ)) x‖ = ‖iteratedDeriv c f x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := f) hf.contDiffAt
    (by exact_mod_cast le_top)

theorem iteratedDeriv_eq_zero_of_eventuallyEq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {x : ℝ} (h : f =ᶠ[𝓝 x] fun _ => 0) (c : ℕ) :
    iteratedDeriv c f x = 0 := by
  rw [h.iteratedDeriv_eq c]
  cases c with
  | zero => simp
  | succ c => simp

theorem chi0_eventually_zero {x : ℝ} (hx : 1 < |x|) : chi0 =ᶠ[𝓝 x] fun _ => 0 := by
  have : ∀ᶠ y in 𝓝 x, 1 < |y| := (continuous_abs.tendsto x).eventually (lt_mem_nhds hx)
  filter_upwards [this] with y hy using chi0_eq_zero hy.le

theorem chiInfinity_eq_zero {x : ℝ} (hx : |x| ≤ 1 / 2) : chiInfinity x = 0 := by
  simp [chiInfinity, chi0_eq_one hx]

theorem chiInvR_eventually_zero {x : ℝ} (hx : |x| < 1 / 2) : chiInvR =ᶠ[𝓝 x] fun _ => 0 := by
  have : ∀ᶠ y in 𝓝 x, |y| < 1 / 2 := (continuous_abs.tendsto x).eventually (gt_mem_nhds hx)
  filter_upwards [this] with y hy
  simp [chiInvR, chiInfinity_eq_zero hy.le]

theorem chiInvR_eq_mul : chiInvR = fun y => chiInfinity y * y⁻¹ :=
  funext fun _ => div_eq_mul_inv _ _

theorem contDiff_chiInvR : ContDiff ℝ ∞ chiInvR := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : |x| < 1 / 2
  · exact contDiffAt_const.congr_of_eventuallyEq (chiInvR_eventually_zero hx)
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    rw [chiInvR_eq_mul]
    exact (chiInfinity_contDiff (n := ⊤)).contDiffAt.mul (contDiffAt_inv ℝ hx0)

/-- **Gevrey bounds with decay for `χ_∞(x)/x`.** -/
theorem chiInvR_gevrey (c : ℕ) (x : ℝ) :
    (1 + |x|) * ‖iteratedDeriv c chiInvR x‖ ≤
      12 * (1 + Real.exp 4) * Achi ^ c * (Nat.factorial (2 * c) : ℝ) := by
  have hCχ : 0 ≤ 1 + Real.exp 4 := by positivity
  by_cases hx : |x| < 1 / 2
  · rw [iteratedDeriv_eq_zero_of_eventuallyEq_zero (chiInvR_eventually_zero hx) c]
    simp only [norm_zero, mul_zero]
    have := Achi_nonneg
    positivity
  · push Not at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
      linarith
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    rw [chiInvR_eq_mul, show (fun y => chiInfinity y * y⁻¹) = chiInfinity * Inv.inv from rfl,
      iteratedDeriv_mul ((chiInfinity_contDiff (n := ⊤)).of_le (by simp)).contDiffAt
        (contDiffAt_inv ℝ hx0)]
    have hinv : ∀ m : ℕ, (1 + |x|) * ‖iteratedDeriv m Inv.inv x‖ ≤
        3 * (Nat.factorial m : ℝ) * 2 ^ m := fun m => by
      rw [iteratedDeriv_eq_iterate, iter_deriv_inv, norm_mul, norm_mul, norm_pow, norm_neg,
        norm_one, one_pow, one_mul, Real.norm_natCast, norm_zpow, Real.norm_eq_abs]
      have h1 : |x| ^ (-1 - (m : ℤ)) = (|x| ^ (m + 1))⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg]
        congr 1
        push_cast
        ring
      rw [h1]
      have h2 : (1 + |x|) ≤ 3 * |x| := by linarith
      have h3 : (1 : ℝ) ≤ 2 ^ m * |x| ^ m := by
        rw [← mul_pow]
        exact one_le_pow₀ (by linarith)
      have hxm : 0 < |x| ^ (m + 1) := pow_pos hxpos _
      rw [show (1 + |x|) * ((Nat.factorial m : ℝ) * (|x| ^ (m + 1))⁻¹) =
          (Nat.factorial m : ℝ) * ((1 + |x|) / |x| ^ (m + 1)) by ring]
      rw [show 3 * (Nat.factorial m : ℝ) * 2 ^ m = (Nat.factorial m : ℝ) * (3 * 2 ^ m) by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ hxm, pow_succ]
      calc 1 + |x| ≤ 3 * |x| := h2
        _ = 3 * |x| * 1 := by ring
        _ ≤ 3 * |x| * (2 ^ m * |x| ^ m) := by gcongr
        _ = _ := by ring
    calc (1 + |x|) * ‖∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * iteratedDeriv i chiInfinity x *
          iteratedDeriv (c - i) Inv.inv x‖
        ≤ ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * ((1 + Real.exp 4) * Achi ^ i *
            (Nat.factorial (2 * i) : ℝ)) * (3 * (Nat.factorial (c - i) : ℝ) * 2 ^ (c - i)) := by
          refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul, Real.norm_natCast]
          have hχ : ‖iteratedDeriv i chiInfinity x‖ ≤
              (1 + Real.exp 4) * Achi ^ i * (Nat.factorial (2 * i) : ℝ) := by
            have := chiInfinity_gevreyTwoBound i x
            rw [← Real.norm_eq_abs] at this
            exact this
          have := hinv (c - i)
          calc (1 + |x|) * ((c.choose i : ℝ) * ‖iteratedDeriv i chiInfinity x‖ *
                ‖iteratedDeriv (c - i) Inv.inv x‖)
              = (c.choose i : ℝ) * ‖iteratedDeriv i chiInfinity x‖ *
                  ((1 + |x|) * ‖iteratedDeriv (c - i) Inv.inv x‖) := by ring
            _ ≤ _ := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hχ (by positivity)) this
                  (by positivity) (by have := Achi_nonneg; positivity)
      _ ≤ ∑ i ∈ Finset.range (c + 1), 3 * (1 + Real.exp 4) * Achi ^ c *
            ((c.choose i : ℝ) * (Nat.factorial (2 * i) : ℝ) *
              (Nat.factorial (2 * (c - i)) : ℝ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hic : i ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hf : (Nat.factorial (c - i) : ℝ) ≤ Nat.factorial (2 * (c - i)) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have h2 : (2 : ℝ) ^ (c - i) ≤ Achi ^ (c - i) :=
            pow_le_pow_left₀ (by norm_num) two_le_Achi _
          have hA : Achi ^ c = Achi ^ i * Achi ^ (c - i) := by
            rw [← pow_add, Nat.add_sub_cancel' hic]
          rw [hA]
          have := Achi_nonneg
          calc (c.choose i : ℝ) * ((1 + Real.exp 4) * Achi ^ i * (Nat.factorial (2 * i) : ℝ)) *
                (3 * (Nat.factorial (c - i) : ℝ) * 2 ^ (c - i))
              ≤ (c.choose i : ℝ) * ((1 + Real.exp 4) * Achi ^ i * (Nat.factorial (2 * i) : ℝ)) *
                (3 * (Nat.factorial (2 * (c - i)) : ℝ) * Achi ^ (c - i)) := by gcongr
            _ = _ := by ring
      _ = 3 * (1 + Real.exp 4) * Achi ^ c * ∑ i ∈ Finset.range (c + 1),
            ((c.choose i : ℝ) * (Nat.factorial (2 * i) : ℝ) *
              (Nat.factorial (2 * (c - i)) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 3 * (1 + Real.exp 4) * Achi ^ c * (4 * (Nat.factorial (2 * c) : ℝ)) := by
          have := Achi_nonneg
          gcongr
          exact Combinatorics.sum_choose_factorial_le c
      _ = _ := by ring

/-- `Φ(x) = χ_∞(x)/(πix)` (DH21 L1000). -/
@[expose] noncomputable def phiR (x : ℝ) : ℂ := (chiInvR x : ℂ) / (π * I)

/-- The `χ_∞` part of `∫_0^v e^{πixu} du` (DH21 L997–L1001). -/
theorem chiInfinity_mul_eInt (x v : ℝ) :
    (chiInfinity x : ℂ) * eInt x v = phiR x * (cexp (π * I * (x * v)) - 1) := by
  by_cases hx : x = 0
  · subst hx
    simp [phiR, chiInvR, chiInfinity_eq_zero (by norm_num : |(0 : ℝ)| ≤ 1 / 2)]
  · rw [eInt_eq_of_ne hx, phiR, chiInvR]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp

end Real

end WaveTurbulence.ClassJR

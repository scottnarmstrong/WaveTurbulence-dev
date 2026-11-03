/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The `π`-normalized Fourier transform of smooth bumps

DH21 writes time kernels as superpositions `∫ M(σ) e^{πiσv} dσ` (e.g. (extraid), L1037, and the
function `M` in the proof of Lemma 5.3, L978). For a smooth compactly supported `f : ℝ → ℂ` we use
`ftπ f σ = ∫ f(2w) e^{-2πiσw} dw = (1/2) ∫ f(v) e^{-πiσv} dv` and prove

* `integral_ftπ_mul_exp`: `∫ ftπ f (σ) e^{πiσv} dσ = f(v)` (Fourier inversion);
* `exists_norm_iteratedDeriv_ftπ_le`: `|∂^n ftπ f (σ)| ≤ K B^n (1 + |σ|)^{-3}` (all derivatives
  decay uniformly, with geometric growth in `n`);
* `integrable_ftπ`.
-/

public section

open MeasureTheory Set Complex Real Filter
open scoped FourierTransform ContDiff

namespace WaveTurbulence.ClassJR

/-- The `π`-normalized Fourier transform `ftπ f σ = (1/2) ∫ f(v) e^{-πiσv} dv`. -/
@[expose] noncomputable def ftπ (f : ℝ → ℂ) : ℝ → ℂ := 𝓕 (fun w : ℝ => f (2 * w))

section Compact

variable {g : ℝ → ℂ}

theorem hasCompactSupport_iteratedDeriv_of (hc : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hc
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem integrable_iteratedDeriv_of_compact (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (n : ℕ) : Integrable (iteratedDeriv n g) :=
  (hg.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_of hc n)

/-- Decay of the Fourier transform of a compactly supported smooth function. -/
theorem norm_fourier_le_of_compact (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ξ : ℝ) :
    ‖𝓕 g ξ‖ ≤ 8 * ((∫ w, ‖g w‖) + ∫ w, ‖iteratedDeriv 3 g w‖) / (1 + |ξ|) ^ 3 := by
  set a := ∫ w, ‖g w‖ with ha_def
  set b := ∫ w, ‖iteratedDeriv 3 g w‖ with hb_def
  have ha : ‖𝓕 g ξ‖ ≤ a := norm_fourier_le_integral_norm g ξ
  have hb : (2 * π * |ξ|) ^ 3 * ‖𝓕 g ξ‖ ≤ b := by
    have h := fourier_iteratedDeriv (N := 3) (n := 3) (hg.of_le (by exact_mod_cast le_top))
      (fun n _ => integrable_iteratedDeriv_of_compact hg hc n) le_rfl
    have := norm_fourier_le_integral_norm (iteratedDeriv 3 g) ξ
    rw [h] at this
    have hn : ‖(2 * π * I * (ξ : ℂ)) ^ 3 • 𝓕 g ξ‖ = (2 * π * |ξ|) ^ 3 * ‖𝓕 g ξ‖ := by
      rw [norm_smul, norm_pow]
      congr 2
      simp [abs_of_pos Real.pi_pos]
    rw [hn] at this
    exact this
  have ha0 : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < (1 + |ξ|) ^ 3 := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_or_gt |ξ| 1 with h1 | h1
  · have h8 : (1 + |ξ|) ^ 3 ≤ 8 := by
      calc (1 + |ξ|) ^ 3 ≤ (1 + 1) ^ 3 := by gcongr
        _ = 8 := by norm_num
    calc ‖𝓕 g ξ‖ * (1 + |ξ|) ^ 3 ≤ a * 8 :=
          mul_le_mul ha h8 (by positivity) ha0
      _ ≤ 8 * (a + b) := by linarith
  · have h2 : (1 + |ξ|) ^ 3 ≤ 8 * |ξ| ^ 3 := by
      have : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      calc (1 + |ξ|) ^ 3 ≤ (2 * |ξ|) ^ 3 := by gcongr
        _ = 8 * |ξ| ^ 3 := by ring
    have h3 : |ξ| ^ 3 * ‖𝓕 g ξ‖ ≤ b := by
      refine le_trans ?_ hb
      have hπ : 1 ≤ 2 * π := by linarith [Real.two_le_pi]
      have : |ξ| ^ 3 ≤ (2 * π * |ξ|) ^ 3 := by
        gcongr
        calc |ξ| = 1 * |ξ| := (one_mul _).symm
          _ ≤ 2 * π * |ξ| := mul_le_mul_of_nonneg_right hπ (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    calc ‖𝓕 g ξ‖ * (1 + |ξ|) ^ 3 ≤ ‖𝓕 g ξ‖ * (8 * |ξ| ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 8 * (|ξ| ^ 3 * ‖𝓕 g ξ‖) := by ring
      _ ≤ 8 * b := by linarith
      _ ≤ 8 * (a + b) := by linarith

theorem integrable_fourier_of_compact (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Integrable (𝓕 g) := by
  have hcont : Continuous (𝓕 g) := by
    refine (contDiff_fourier (N := 0) fun n hn => ?_).continuous
    have : n = 0 := by exact_mod_cast le_zero_iff.mp hn
    subst this
    simpa using (hg.continuous.integrable_of_hasCompactSupport hc).norm
  set C := 8 * ((∫ w, ‖g w‖) + ∫ w, ‖iteratedDeriv 3 g w‖)
  refine ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by norm_num)).const_mul
    C).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa [div_eq_mul_inv] using norm_fourier_le_of_compact hg hc ξ

/-- Fourier inversion for compactly supported smooth functions. -/
theorem fourierInv_fourier_of_compact (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    𝓕⁻ (𝓕 g) = g :=
  Continuous.fourierInv_fourier_eq hg.continuous
    (hg.continuous.integrable_of_hasCompactSupport hc) (integrable_fourier_of_compact hg hc)

end Compact

section Ftpi

variable {f : ℝ → ℂ}

theorem contDiff_comp_two (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun w : ℝ => f (2 * w)) :=
  hf.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_comp_two (hc : HasCompactSupport f) :
    HasCompactSupport (fun w : ℝ => f (2 * w)) :=
  hc.comp_homeomorph (Homeomorph.mulLeft₀ (2 : ℝ) two_ne_zero)

/-- **Fourier inversion** in the `π` normalization. -/
theorem integral_ftπ_mul_exp (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : ℝ) :
    ∫ σ, ftπ f σ * cexp (π * I * σ * v) = f v := by
  have h := congrFun (fourierInv_fourier_of_compact (contDiff_comp_two hf)
    (hasCompactSupport_comp_two hc)) (v / 2)
  rw [fourierInv_eq'] at h
  rw [show 2 * (v / 2) = v by ring] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
  simp only [ftπ, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

theorem integrable_pow_smul_comp_two (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k • f (2 * x)) := by
  exact ((continuous_pow k).smul (contDiff_comp_two hf).continuous).integrable_of_hasCompactSupport
    ((hasCompactSupport_comp_two hc).smul_left (f := fun x : ℝ => x ^ k))

/-- The derivatives of `ftπ f`. -/
theorem iteratedDeriv_ftπ (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    iteratedDeriv n (ftπ f) = 𝓕 (fun w : ℝ => (-2 * π * I * w) ^ n • f (2 * w)) :=
  iteratedDeriv_fourier (N := ⊤) (fun k _ => integrable_pow_smul_comp_two hf hc k) le_top

end Ftpi

section Bounds

theorem tsupport_iteratedDeriv_subset' {g : ℝ → ℂ} (n : ℕ) :
    tsupport (iteratedDeriv n g) ⊆ tsupport g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- `n^i ≤ 3^n` for `i ≤ 3`. -/
theorem pow_le_three_pow {n i : ℕ} (hi : i ≤ 3) : n ^ i ≤ 3 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · simp [Nat.zero_pow hi0]
  · calc n ^ i ≤ n ^ 3 := Nat.pow_le_pow_right hn hi
      _ ≤ 3 ^ n := by
        induction n with
        | zero => simp
        | succ m ih =>
          rcases Nat.lt_or_ge m 3 with hm | hm
          · interval_cases m <;> norm_num
          · have := ih (by omega)
            calc (m + 1) ^ 3 ≤ 3 * m ^ 3 := by
                  have h1 : (m + 1) ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by ring
                  have h2 : 3 * m ^ 2 ≤ m ^ 3 := by nlinarith
                  have h3 : 3 * m + 1 ≤ m ^ 3 := by nlinarith
                  omega
              _ ≤ 3 * 3 ^ m := by omega
              _ = 3 ^ (m + 1) := by ring

/-- The derivatives of the monomial `(-2πi w)^n`. -/
theorem norm_iteratedDeriv_monomial_le (n i : ℕ) (w : ℝ) :
    ‖iteratedDeriv i (fun w : ℝ => (-2 * π * I * w) ^ n) w‖ ≤
      (2 * π) ^ n * (n : ℝ) ^ i * |w| ^ (n - i) := by
  have hfun : (fun w : ℝ => (-2 * π * I * w) ^ n) =
      ((-2 * π * I) ^ n) • (Complex.ofRealCLM ∘ fun w : ℝ => w ^ n) := by
    funext w
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Complex.ofRealCLM_apply,
      Complex.ofReal_pow]
    ring
  have hc : ContDiff ℝ ∞ (fun w : ℝ => w ^ n) := contDiff_id.pow n
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfun,
    iteratedFDeriv_const_smul_apply ((Complex.ofRealCLM.contDiff.comp hc).contDiffAt.of_le
      (by exact_mod_cast le_top)),
    Complex.ofRealCLM.iteratedFDeriv_comp_left hc.contDiffAt (by exact_mod_cast le_top), norm_smul]
  have h1 : ‖(-2 * π * I) ^ n‖ = (2 * π) ^ n := by
    rw [norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hL : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  refine (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans ?_
  rw [one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_pow, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  gcongr
  rw [Nat.abs_cast]
  exact_mod_cast Nat.descFactorial_le_pow n i

variable {f : ℝ → ℂ}

/-- **Uniform decay of all derivatives of `ftπ f`**, with geometric growth in the order. -/
theorem exists_norm_iteratedDeriv_ftπ_le (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ n ξ, ‖iteratedDeriv n (ftπ f) ξ‖ ≤ K * B ^ n / (1 + |ξ|) ^ 3 := by
  set g := fun w : ℝ => f (2 * w) with hg_def
  have hg : ContDiff ℝ ∞ g := contDiff_comp_two hf
  have hgc : HasCompactSupport g := hasCompactSupport_comp_two hc
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRw : ∀ w ∈ tsupport g, |w| ≤ R := fun w hw => by
    have := hR₀ hw
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hzero : ∀ j w, w ∉ tsupport g → iteratedDeriv j g w = 0 := fun j w hw =>
    image_eq_zero_of_notMem_tsupport (fun h => hw (tsupport_iteratedDeriv_subset' j h))
  set S := ∑ j ∈ Finset.range 4, ∫ w, ‖iteratedDeriv j g w‖ with hS
  have hint : ∀ j, Integrable (fun w => ‖iteratedDeriv j g w‖) := fun j =>
    (integrable_iteratedDeriv_of_compact hg hgc j).norm
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _
  set B := 2 * π * 3 * R
  have hB0 : 0 ≤ B := by positivity
  refine ⟨32 * S, B, by positivity, hB0, fun n ξ => ?_⟩
  set p : ℝ → ℂ := fun w => (-2 * π * I * w) ^ n
  have hp : ContDiff ℝ ∞ p := (contDiff_const.mul Complex.ofRealCLM.contDiff).pow n
  set h : ℝ → ℂ := fun w => p w * g w
  have hh : ContDiff ℝ ∞ h := hp.mul hg
  have hhc : HasCompactSupport h := hgc.mul_left
  have hpb : ∀ i ≤ 3, ∀ w ∈ tsupport g, ‖iteratedDeriv i p w‖ ≤ B ^ n := fun i hi w hw => by
    refine (norm_iteratedDeriv_monomial_le n i w).trans ?_
    have h3 : ((n : ℝ) ^ i) ≤ 3 ^ n := by exact_mod_cast pow_le_three_pow hi
    have hRn : |w| ^ (n - i) ≤ R ^ n :=
      (pow_le_pow_left₀ (abs_nonneg w) (hRw w hw) _).trans (pow_le_pow_right₀ hR1 (Nat.sub_le n i))
    calc (2 * π) ^ n * (n : ℝ) ^ i * |w| ^ (n - i) ≤ (2 * π) ^ n * 3 ^ n * R ^ n := by gcongr
      _ = B ^ n := by simp only [B]; rw [mul_pow (2 * π * 3), mul_pow (2 * π)]
  -- the derivative formula
  have hD : iteratedDeriv n (ftπ f) ξ = 𝓕 h ξ := by
    rw [iteratedDeriv_ftπ hf hc]
    rfl
  rw [hD]
  refine (norm_fourier_le_of_compact hh hhc ξ).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  -- bound the two integrals
  have hA : ∫ w, ‖h w‖ ≤ B ^ n * S := by
    calc ∫ w, ‖h w‖ ≤ ∫ w, B ^ n * ‖iteratedDeriv 0 g w‖ := by
          refine integral_mono (hh.continuous.integrable_of_hasCompactSupport hhc).norm
            ((hint 0).const_mul _) fun w => ?_
          by_cases hw : w ∈ tsupport g
          · simp only [h, norm_mul, iteratedDeriv_zero]
            exact mul_le_mul_of_nonneg_right (by simpa using hpb 0 (by norm_num) w hw)
              (norm_nonneg _)
          · have := hzero 0 w hw
            simp only [iteratedDeriv_zero] at this
            simp [h, this]
      _ = B ^ n * ∫ w, ‖iteratedDeriv 0 g w‖ := integral_const_mul _ _
      _ ≤ B ^ n * S := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.single_le_sum (f := fun j => ∫ w, ‖iteratedDeriv j g w‖)
            (fun _ _ => integral_nonneg fun _ => norm_nonneg _) (by simp)
  have hB3 : ∫ w, ‖iteratedDeriv 3 h w‖ ≤ 3 * (B ^ n * S) := by
    have hpt : ∀ w, ‖iteratedDeriv 3 h w‖ ≤
        3 * B ^ n * ∑ j ∈ Finset.range 4, ‖iteratedDeriv j g w‖ := fun w => by
      rw [show h = p * g from rfl, iteratedDeriv_mul (hp.of_le (by simp)).contDiffAt
        (hg.of_le (by simp)).contDiffAt]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      by_cases hw : w ∈ tsupport g
      · calc ∑ i ∈ Finset.range 4, ‖(Nat.choose 3 i : ℂ) * iteratedDeriv i p w *
              iteratedDeriv (3 - i) g w‖
            ≤ ∑ i ∈ Finset.range 4, 3 * B ^ n * ‖iteratedDeriv (3 - i) g w‖ := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi3 : i ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              rw [norm_mul, norm_mul, Complex.norm_natCast]
              have hc3 : (Nat.choose 3 i : ℝ) ≤ 3 := by
                interval_cases i <;> norm_num [Nat.choose]
              have := hpb i hi3 w hw
              gcongr
          _ = ∑ j ∈ Finset.range 4, 3 * B ^ n * ‖iteratedDeriv j g w‖ := by
              rw [← Finset.sum_range_reflect]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hi3 : i < 4 := Finset.mem_range.mp hi
              congr 3
              omega
      · have : ∀ j, iteratedDeriv j g w = 0 := fun j => hzero j w hw
        simp [this]
    calc ∫ w, ‖iteratedDeriv 3 h w‖
        ≤ ∫ w, 3 * B ^ n * ∑ j ∈ Finset.range 4, ‖iteratedDeriv j g w‖ :=
          integral_mono (integrable_iteratedDeriv_of_compact hh hhc 3).norm
            ((integrable_finsetSum _ fun j _ => hint j).const_mul _) hpt
      _ = 3 * (B ^ n * S) := by
          rw [integral_const_mul, integral_finsetSum _ fun j _ => hint j]
          ring
  calc 8 * ((∫ w, ‖h w‖) + ∫ w, ‖iteratedDeriv 3 h w‖) ≤ 8 * (B ^ n * S + 3 * (B ^ n * S)) := by
        gcongr
    _ = 32 * S * B ^ n := by ring

/-- `ftπ f` is integrable. -/
theorem integrable_ftπ (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (ftπ f) :=
  integrable_fourier_of_compact (contDiff_comp_two hf) (hasCompactSupport_comp_two hc)

/-- `ftπ f` is smooth. -/
theorem contDiff_ftπ (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ContDiff ℝ ∞ (ftπ f) :=
  contDiff_fourier (N := ⊤) fun k _ => by
    simpa [norm_smul, norm_pow] using (integrable_pow_smul_comp_two hf hc k).norm

end Bounds

end WaveTurbulence.ClassJR

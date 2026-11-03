/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SeriesTools
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Taylor series `S(σ) = Σ σⁿ aₙ` as a Schwartz function

For Schwartz data `φ₀` let `X₀ = lowConst φ₀` (a bound for `(1 + |y|)^{2d+1} |φ₀(y)|`),
`ρ = taylorRho φ₀ = taylorRate d (2d+1) X₀` and `T = solTime φ₀ = 1/(4(ρ+1))`. By
`multBound_taylorCoeff`, for every `r, w`:
`(1 + |y|)^{w+2d+1} ‖Dʳ aₙ(y)‖ ≤ ((2n+1) Y_{r,w})^{r+w} X₀ ρⁿ` (`coeff_bound`). Hence for `|σ| ≤ T`
the series converges in every Schwartz seminorm (`taylorSchwartz`), and `σ ↦ S(σ)` is Lipschitz
into each seminorm on `[-T, T]` (`seminorm_taylorSchwartz_sub_le`).
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence.WKE

variable {d : ℕ}

theorem exists_weighted_bound (f : 𝓢(Mom d, ℝ)) (r : ℕ) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ s * ‖iteratedFDeriv ℝ r f x‖ ≤ C := by
  set k : ℕ := ⌈s⌉₊
  set S : ℝ := 2 ^ k * (Finset.Iic (k, r)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨S, hS, fun x => ?_⟩
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, r)) le_rfl le_rfl f x
  have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpow : (1 + ‖x‖) ^ s ≤ (1 + ‖x‖) ^ k := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil s)
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hb

section Constants

variable (φ₀ : 𝓢(Mom d, ℝ))

/-- The low norm `sup_y (1 + |y|)^{2d+1} |φ₀(y)|`, plus one (so that it is positive). -/
@[expose] noncomputable def lowConst : ℝ :=
  sSup (Set.range fun y : Mom d => (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * ‖iteratedFDeriv ℝ 0 φ₀ y‖) + 1

theorem bddAbove_lowNorm :
    BddAbove (Set.range fun y : Mom d => (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) *
      ‖iteratedFDeriv ℝ 0 φ₀ y‖) := by
  obtain ⟨C, -, hC⟩ := exists_weighted_bound φ₀ 0 (2 * d + 1)
  exact ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩

theorem lowConst_bound (y : Mom d) :
    (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * ‖iteratedFDeriv ℝ 0 φ₀ y‖ ≤ lowConst φ₀ := by
  have := le_csSup (bddAbove_lowNorm φ₀) (Set.mem_range_self y)
  unfold lowConst; linarith

theorem lowConst_pos : 0 < lowConst φ₀ := by
  have h := lowConst_bound φ₀ 0
  have : 0 ≤ (1 + ‖(0 : Mom d)‖) ^ (2 * (d : ℝ) + 1) * ‖iteratedFDeriv ℝ 0 φ₀ 0‖ := by positivity
  have h1 := le_csSup (bddAbove_lowNorm φ₀) (Set.mem_range_self 0)
  unfold lowConst; linarith

/-- If the low norm is at most `B`, then `lowConst φ₀ ≤ B + 1`. -/
theorem lowConst_le {B : ℝ} (hB : ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ₀ y| ≤ B) :
    lowConst φ₀ ≤ B + 1 := by
  have : sSup (Set.range fun y : Mom d => (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) *
      ‖iteratedFDeriv ℝ 0 φ₀ y‖) ≤ B := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨y, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hB y
  unfold lowConst; linarith

/-- The geometric rate of the Taylor coefficients of the solution with data `φ₀`. -/
@[expose] noncomputable def taylorRho : ℝ := taylorRate d (2 * d + 1) (lowConst φ₀)

theorem taylorRho_nonneg : 0 ≤ taylorRho φ₀ := taylorRate_nonneg _ _ _

/-- The existence time of the power-series solution: `T = 1 / (4 (ρ + 1))`. -/
@[expose] noncomputable def solTime : ℝ := 1 / (4 * (taylorRho φ₀ + 1))

theorem solTime_pos : 0 < solTime φ₀ := by
  have := taylorRho_nonneg φ₀; unfold solTime; positivity

theorem solTime_mul_rho : solTime φ₀ * taylorRho φ₀ ≤ 1 / 4 := by
  have h := taylorRho_nonneg φ₀
  unfold solTime
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem exists_multBound_base (R W : ℕ) :
    ∃ Y, 0 ≤ Y ∧ MultBound R W (2 * d + 1) 1 Y (lowConst φ₀) φ₀ := by
  have hX := lowConst_pos φ₀
  choose C hC0 hC using fun (p : ℕ × ℕ) => exists_weighted_bound φ₀ p.1 ((p.2 : ℝ) + (2 * d + 1))
  set Y : ℝ := 1 + ∑ r ∈ range (R + 1), ∑ w ∈ range (W + 1), C (r, w) / lowConst φ₀
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ ∑ r ∈ range (R + 1), ∑ w ∈ range (W + 1), C (r, w) / lowConst φ₀ :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun w _ => div_nonneg (hC0 _) hX.le
    simp only [Y]; linarith
  refine ⟨Y, by linarith, fun r hr w hw y => ?_⟩
  rw [one_mul]
  rcases Nat.eq_zero_or_pos (r + w) with h | h
  · obtain ⟨rfl, rfl⟩ : r = 0 ∧ w = 0 := by omega
    simpa using lowConst_bound φ₀ y
  · have hCY : C (r, w) ≤ Y * lowConst φ₀ := by
      have hle : C (r, w) / lowConst φ₀ ≤ Y := by
        have h1 : C (r, w) / lowConst φ₀ ≤
            ∑ r' ∈ range (R + 1), ∑ w' ∈ range (W + 1), C (r', w') / lowConst φ₀ := by
          have hr' : r ∈ range (R + 1) := mem_range.mpr (by omega)
          have hw' : w ∈ range (W + 1) := mem_range.mpr (by omega)
          refine (Finset.single_le_sum (f := fun w' => C (r, w') / lowConst φ₀)
            (fun w' _ => div_nonneg (hC0 _) hX.le) hw').trans ?_
          exact Finset.single_le_sum (f := fun r' => ∑ w' ∈ range (W + 1),
            C (r', w') / lowConst φ₀) (fun r' _ => Finset.sum_nonneg fun w' _ =>
              div_nonneg (hC0 _) hX.le) hr'
        simp only [Y]; linarith
      rwa [div_le_iff₀ hX] at hle
    have hYp : Y ≤ Y ^ (r + w) := by
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (r + w) := pow_le_pow_right₀ hY1 h
    calc (1 + ‖y‖) ^ ((w : ℝ) + (2 * d + 1)) * ‖iteratedFDeriv ℝ r φ₀ y‖ ≤ C (r, w) := hC (r, w) y
      _ ≤ Y * lowConst φ₀ := hCY
      _ ≤ Y ^ (r + w) * lowConst φ₀ := mul_le_mul_of_nonneg_right hYp hX.le

/-- The base constant `Y_{R,W}`. -/
@[expose] noncomputable def baseY (R W : ℕ) : ℝ := (exists_multBound_base φ₀ R W).choose

theorem baseY_nonneg (R W : ℕ) : 0 ≤ baseY φ₀ R W := (exists_multBound_base φ₀ R W).choose_spec.1

theorem multBound_base (R W : ℕ) :
    MultBound R W (2 * d + 1) 1 (baseY φ₀ R W) (lowConst φ₀) φ₀ :=
  (exists_multBound_base φ₀ R W).choose_spec.2

end Constants

section Coeffs

variable (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ))

/-- The weighted bound for the Taylor coefficients. -/
theorem coeff_bound (r w n : ℕ) (y : Mom d) :
    (1 + ‖y‖) ^ ((w : ℝ) + (2 * d + 1)) * ‖iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) y‖ ≤
      ((2 * n + 1) * baseY φ₀ r w) ^ (r + w) * lowConst φ₀ * taylorRho φ₀ ^ n := by
  have hb := multBound_taylorCoeff hd (by linarith) (baseY_nonneg φ₀ r w) (multBound_base φ₀ r w) n
    r le_rfl w le_rfl y
  refine hb.trans ?_
  have hX := (lowConst_pos φ₀).le
  have hρ := taylorRho_nonneg φ₀
  have hY := baseY_nonneg φ₀ r w
  have h1 : lowConst φ₀ * taylorRate d (2 * d + 1) (lowConst φ₀) ^ n / ((n : ℝ) + 1) ^ 2 ≤
      lowConst φ₀ * taylorRho φ₀ ^ n := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h0 : 0 ≤ lowConst φ₀ * taylorRho φ₀ ^ n := by positivity
    unfold taylorRho at h0 ⊢
    nlinarith
  calc ((2 * (n : ℝ) + 1) * baseY φ₀ r w) ^ (r + w) * (lowConst φ₀ *
        taylorRate d (2 * d + 1) (lowConst φ₀) ^ n / ((n : ℝ) + 1) ^ 2)
      ≤ ((2 * (n : ℝ) + 1) * baseY φ₀ r w) ^ (r + w) * (lowConst φ₀ * taylorRho φ₀ ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem abs_coeff_le (n : ℕ) (y : Mom d) :
    |taylorCoeff hd φ₀ n y| ≤ lowConst φ₀ * taylorRho φ₀ ^ n * (1 + ‖y‖) ^ (-(2 * (d : ℝ) + 1)) := by
  have h := coeff_bound hd φ₀ 0 0 n y
  simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs] at h
  have := le_of_weighted (w := 0) (s₀ := 2 * d + 1) y (by simpa using h)
  simpa [wt] using this

theorem norm_iteratedFDeriv_coeff_le (r m n : ℕ) (x : Mom d) :
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) x‖ ≤
      ((2 * n + 1) * baseY φ₀ r m) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n := by
  refine le_trans ?_ (coeff_bound hd φ₀ r m n x)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m := pow_le_pow_left₀ (norm_nonneg x) (by linarith) m
    _ = (1 + ‖x‖) ^ (m : ℝ) := (Real.rpow_natCast _ m).symm
    _ ≤ (1 + ‖x‖) ^ ((m : ℝ) + (2 * d + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
          (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])

end Coeffs

/-! ### Summability -/

theorem summable_coeff_weights {Y X ρ q : ℝ} (p : ℕ) (hq0 : 0 ≤ q)
    (hq : ρ * q ≤ 1 / 2) (hρ : 0 ≤ ρ) :
    Summable (fun n : ℕ => ((2 * n + 1) * Y) ^ p * X * ρ ^ n * q ^ n) := by
  have hs := (summable_two_mul_add_one_pow_mul_geometric p (q := ρ * q) (by positivity)
    (by linarith)).mul_left (Y ^ p * X)
  refine hs.congr fun n => ?_
  push_cast; rw [mul_pow, mul_pow]; ring

/-- `n qⁿ⁻¹ ≤ (2n+1) qⁿ / q` for `q > 0`. -/
theorem nat_mul_pow_pred_le {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (n : ℝ) * q ^ (n - 1) ≤ (2 * n + 1) * q ^ n / q := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp; positivity
  · have e : q ^ n = q ^ (n - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel h]
    rw [e, le_div_iff₀ hq]
    have hA : 0 ≤ q ^ (n - 1) * q := by positivity
    have := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ 2 * n + 1 by linarith) hA
    linarith

section Series

variable (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ))

/-- The `n`-th term `σⁿ aₙ`. -/
@[expose] noncomputable def taylorTerm (σ : ℝ) (n : ℕ) : 𝓢(Mom d, ℝ) := σ ^ n • taylorCoeff hd φ₀ n

theorem norm_iteratedFDeriv_taylorTerm_le (σ : ℝ) (r m n : ℕ) (x : Mom d) :
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x‖ ≤
      ((2 * n + 1) * baseY φ₀ r m) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n * |σ| ^ n := by
  have e : iteratedFDeriv ℝ r (⇑(taylorTerm hd φ₀ σ n)) x =
      σ ^ n • iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) x :=
    iteratedFDeriv_const_smul_apply ((taylorCoeff hd φ₀ n).smooth r).contDiffAt
  rw [e, norm_smul, Real.norm_eq_abs, abs_pow]
  have := norm_iteratedFDeriv_coeff_le hd φ₀ r m n x
  calc ‖x‖ ^ m * (|σ| ^ n * ‖iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) x‖)
      = |σ| ^ n * (‖x‖ ^ m * ‖iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) x‖) := by ring
    _ ≤ |σ| ^ n * (((2 * n + 1) * baseY φ₀ r m) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem summable_taylor_bound {σ : ℝ} (hσ : |σ| ≤ 2 * solTime φ₀) (r m : ℕ) :
    Summable (fun n : ℕ => ((2 * n + 1) * baseY φ₀ r m) ^ (r + m) * lowConst φ₀ *
      taylorRho φ₀ ^ n * |σ| ^ n) := by
  refine summable_coeff_weights (Y := baseY φ₀ r m) (r + m) (abs_nonneg σ) ?_
    (taylorRho_nonneg φ₀)
  have h := solTime_mul_rho φ₀
  have hρ := taylorRho_nonneg φ₀
  nlinarith [mul_le_mul_of_nonneg_left hσ hρ]

/-- The series `Σ σⁿ aₙ(y)`. -/
@[expose] noncomputable def taylorFun (σ : ℝ) (y : Mom d) : ℝ := ∑' n, taylorTerm hd φ₀ σ n y

theorem contDiff_taylorFun {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (taylorFun hd φ₀ σ) := by
  have hσ2 : |σ| ≤ 2 * solTime φ₀ := by linarith [solTime_pos φ₀]
  refine contDiff_tsum (f := fun n => ⇑(taylorTerm hd φ₀ σ n))
    (v := fun k n => ((2 * n + 1) * baseY φ₀ k 0) ^ (k + 0) * lowConst φ₀ *
      taylorRho φ₀ ^ n * |σ| ^ n) (fun n => (taylorTerm hd φ₀ σ n).smooth ⊤)
    (fun k _ => summable_taylor_bound φ₀ hσ2 k 0) (fun k n x _ => ?_)
  simpa using norm_iteratedFDeriv_taylorTerm_le hd φ₀ σ k 0 n x

theorem iteratedFDeriv_taylorFun {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (r : ℕ) (x : Mom d) :
    iteratedFDeriv ℝ r (taylorFun hd φ₀ σ) x =
      ∑' n, iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x := by
  have hσ2 : |σ| ≤ 2 * solTime φ₀ := by linarith [solTime_pos φ₀]
  exact iteratedFDeriv_tsum_apply (f := fun n => ⇑(taylorTerm hd φ₀ σ n))
    (v := fun k n => ((2 * n + 1) * baseY φ₀ k 0) ^ (k + 0) * lowConst φ₀ *
      taylorRho φ₀ ^ n * |σ| ^ n) (fun n => (taylorTerm hd φ₀ σ n).smooth ⊤)
    (fun k _ => summable_taylor_bound φ₀ hσ2 k 0)
    (fun k n x _ => by simpa using norm_iteratedFDeriv_taylorTerm_le hd φ₀ σ k 0 n x) le_top x

theorem decay_taylorFun {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (m r : ℕ) (x : Mom d) :
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ r (taylorFun hd φ₀ σ) x‖ ≤
      ∑' n : ℕ, ((2 * n + 1) * baseY φ₀ r m) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n *
        |σ| ^ n := by
  have hσ2 : |σ| ≤ 2 * solTime φ₀ := by linarith [solTime_pos φ₀]
  have hsum := summable_taylor_bound φ₀ hσ2 r m
  have hsum0 := summable_taylor_bound φ₀ hσ2 r 0
  rw [iteratedFDeriv_taylorFun hd φ₀ hσ r x]
  have hnorm : Summable (fun n => ‖iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by simpa using norm_iteratedFDeriv_taylorTerm_le hd φ₀ σ r 0 n x) hsum0
  calc ‖x‖ ^ m * ‖∑' n, iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x‖
      ≤ ‖x‖ ^ m * ∑' n, ‖iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by positivity)
    _ = ∑' n, ‖x‖ ^ m * ‖iteratedFDeriv ℝ r (taylorTerm hd φ₀ σ n) x‖ := tsum_mul_left.symm
    _ ≤ _ := (hnorm.mul_left _).tsum_le_tsum
        (fun n => norm_iteratedFDeriv_taylorTerm_le hd φ₀ σ r m n x) hsum

/-- The Taylor sum `S(σ) = Σ σⁿ aₙ` as a Schwartz function, for `|σ| ≤ T`. -/
@[expose] noncomputable def taylorSchwartz {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) : 𝓢(Mom d, ℝ) where
  toFun := taylorFun hd φ₀ σ
  smooth' := contDiff_taylorFun hd φ₀ hσ
  decay' m r := ⟨_, decay_taylorFun hd φ₀ hσ m r⟩

theorem taylorSchwartz_apply {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (y : Mom d) :
    taylorSchwartz hd φ₀ hσ y = ∑' n, σ ^ n * taylorCoeff hd φ₀ n y := by
  change taylorFun hd φ₀ σ y = _
  simp [taylorFun, taylorTerm]

end Series

end WaveTurbulence.WKE

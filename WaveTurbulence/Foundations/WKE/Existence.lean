/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.TaylorSeries
public import WaveTurbulence.Foundations.WKE.Lifespan
public import WaveTurbulence.Foundations.WKE.Uniqueness
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Local existence of Schwartz solutions of (WKE) by power series; `τ_max`

* `isWKESolution_taylorSol`: for Schwartz data `φ₀`, the Taylor sum `τ ↦ S(τ) = Σ τⁿ aₙ` is a
  Schwartz-class solution on `[0, T]`, `T = solTime φ₀ = 1/(4(ρ+1))`, `ρ` depending only on the
  low norm `sup (1+|y|)^{2d+1}|φ₀(y)|` (TARGET Prop `wkelwp`, existence; (wketaylor) L753).
* `exists_isWKESolution`: local existence.
* `tauMax_pos`, `lt_tauMax_iff`, `wkelwp_conj12`: TARGET Prop `wkelwp` (L598–L601), conjuncts 1–2
  as frozen: `0 < τ_max`, `ofReal τ★ < τ_max ↔ ∃ φ, IsWKESolution φin τ★ φ`, and uniqueness.
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence.WKE

variable {d : ℕ}

section Solution

variable (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ))

/-- Clamp `τ` into `[0, T]`. -/
@[expose] noncomputable def clampT (τ : ℝ) : ℝ := max 0 (min τ (solTime φ₀))

theorem abs_clampT_le (τ : ℝ) : |clampT φ₀ τ| ≤ solTime φ₀ := by
  have hT := (solTime_pos φ₀).le
  unfold clampT
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le hT (min_le_right _ _)

theorem clampT_of_mem {τ : ℝ} (h : τ ∈ Icc 0 (solTime φ₀)) : clampT φ₀ τ = τ := by
  unfold clampT; rw [min_eq_left h.2, max_eq_right h.1]

theorem abs_clampT_sub_le (τ τ' : ℝ) : |clampT φ₀ τ' - clampT φ₀ τ| ≤ |τ' - τ| := by
  unfold clampT
  calc |max 0 (min τ' (solTime φ₀)) - max 0 (min τ (solTime φ₀))|
      ≤ |min τ' (solTime φ₀) - min τ (solTime φ₀)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ max |τ' - τ| |solTime φ₀ - solTime φ₀| := abs_min_sub_min_le_max _ _ _ _
    _ = |τ' - τ| := by simp

/-- The power-series solution `τ ↦ S(clamp τ)`. -/
@[expose] noncomputable def taylorSol (τ : ℝ) : 𝓢(Mom d, ℝ) :=
  taylorSchwartz hd φ₀ (abs_clampT_le φ₀ τ)

theorem taylorSol_apply (τ : ℝ) (y : Mom d) :
    taylorSol hd φ₀ τ y = ∑' n, clampT φ₀ τ ^ n * taylorCoeff hd φ₀ n y :=
  taylorSchwartz_apply hd φ₀ _ y

theorem taylorSol_zero : taylorSol hd φ₀ 0 = φ₀ := by
  ext y
  rw [taylorSol_apply, clampT_of_mem φ₀ ⟨le_rfl, (solTime_pos φ₀).le⟩,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp [taylorCoeff_zero]

/-! ### Continuity into `𝓢` -/

/-- The Lipschitz constant of `σ ↦ S(σ)` in the seminorm `(m, r)`. -/
@[expose] noncomputable def lipConst (m r : ℕ) : ℝ :=
  (∑' n : ℕ, ((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m + 1) * lowConst φ₀ * taylorRho φ₀ ^ n *
    solTime φ₀ ^ n) / solTime φ₀

theorem summable_lip (m r : ℕ) : Summable (fun n : ℕ =>
    ((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m + 1) * lowConst φ₀ * taylorRho φ₀ ^ n *
      solTime φ₀ ^ n) :=
  summable_coeff_weights (r + m + 1) (solTime_pos φ₀).le
    (by have := solTime_mul_rho φ₀; nlinarith) (taylorRho_nonneg φ₀)

theorem seminorm_taylorSchwartz_sub_le {σ σ' : ℝ} (hσ : |σ| ≤ solTime φ₀)
    (hσ' : |σ'| ≤ solTime φ₀) (m r : ℕ) :
    SchwartzMap.seminorm ℝ m r (taylorSchwartz hd φ₀ hσ' - taylorSchwartz hd φ₀ hσ) ≤
      lipConst φ₀ m r * |σ' - σ| := by
  have hT := solTime_pos φ₀
  have hσ2 : |σ| ≤ 2 * solTime φ₀ := by linarith
  have hσ2' : |σ'| ≤ 2 * solTime φ₀ := by linarith
  have hY := baseY_nonneg φ₀ r m
  have hX := (lowConst_pos φ₀).le
  have hρ := taylorRho_nonneg φ₀
  have hL : 0 ≤ lipConst φ₀ m r := by
    unfold lipConst
    exact div_nonneg (tsum_nonneg fun n => by positivity) hT.le
  refine SchwartzMap.seminorm_le_bound ℝ m r _ (by positivity) fun x => ?_
  -- the iterated derivative of the difference, termwise
  set D := fun n : ℕ => iteratedFDeriv ℝ r (taylorCoeff hd φ₀ n) x
  have hterm : ∀ (τ : ℝ) (n : ℕ),
      iteratedFDeriv ℝ r (⇑(taylorTerm hd φ₀ τ n)) x = τ ^ n • D n := fun τ n =>
    iteratedFDeriv_const_smul_apply ((taylorCoeff hd φ₀ n).smooth r).contDiffAt
  have hsn : ∀ {τ : ℝ}, |τ| ≤ 2 * solTime φ₀ → Summable (fun n => ‖τ ^ n • D n‖) := by
    intro τ hτ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_taylor_bound φ₀ hτ r 0)
    rw [← hterm]
    simpa using norm_iteratedFDeriv_taylorTerm_le hd φ₀ τ r 0 n x
  have hs : ∀ {τ : ℝ}, |τ| ≤ 2 * solTime φ₀ → Summable (fun n => τ ^ n • D n) :=
    fun hτ => (hsn hτ).of_norm
  have e : iteratedFDeriv ℝ r (⇑(taylorSchwartz hd φ₀ hσ' - taylorSchwartz hd φ₀ hσ)) x =
      ∑' n, (σ' ^ n - σ ^ n) • D n := by
    rw [FunLike.coe_sub, iteratedFDeriv_sub_apply
      ((taylorSchwartz hd φ₀ hσ').smooth r).contDiffAt ((taylorSchwartz hd φ₀ hσ).smooth r).contDiffAt]
    change iteratedFDeriv ℝ r (taylorFun hd φ₀ σ') x - iteratedFDeriv ℝ r (taylorFun hd φ₀ σ) x = _
    rw [iteratedFDeriv_taylorFun hd φ₀ hσ', iteratedFDeriv_taylorFun hd φ₀ hσ]
    simp_rw [hterm]
    rw [← (hs hσ2').tsum_sub (hs hσ2)]
    simp_rw [sub_smul]
  rw [e]
  -- bound each term
  have hb : ∀ n : ℕ, ‖x‖ ^ m * ‖(σ' ^ n - σ ^ n) • D n‖ ≤
      |σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m + 1) * lowConst φ₀ *
        taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀) := by
    intro n
    have h1 := norm_iteratedFDeriv_coeff_le hd φ₀ r m n x
    have h2 : |σ' ^ n - σ ^ n| ≤ |σ' - σ| * ((2 * n + 1) * solTime φ₀ ^ n / solTime φ₀) := by
      refine (abs_pow_sub_pow_le σ' σ n).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmax : max |σ'| |σ| ≤ solTime φ₀ := max_le hσ' hσ
      calc (n : ℝ) * max |σ'| |σ| ^ (n - 1) ≤ (n : ℝ) * solTime φ₀ ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax _) (by positivity)
        _ ≤ _ := nat_mul_pow_pred_le hT n
    have h3 : ((2 * n + 1) * baseY φ₀ r m) ^ (r + m) ≤
        ((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) _
    rw [norm_smul, Real.norm_eq_abs]
    calc ‖x‖ ^ m * (|σ' ^ n - σ ^ n| * ‖D n‖) = |σ' ^ n - σ ^ n| * (‖x‖ ^ m * ‖D n‖) := by ring
      _ ≤ (|σ' - σ| * ((2 * n + 1) * solTime φ₀ ^ n / solTime φ₀)) *
          (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n) := by
          have h1' : ‖x‖ ^ m * ‖D n‖ ≤
              ((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n :=
            h1.trans (by gcongr)
          exact mul_le_mul h2 h1' (by positivity) (by positivity)
      _ ≤ |σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m + 1) * lowConst φ₀ *
          taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀) := by
          rw [pow_succ]
          have hY1 : (2 * (n : ℝ) + 1) ≤ (2 * n + 1) * (baseY φ₀ r m + 1) :=
            le_mul_of_one_le_right (by positivity) (by linarith)
          have : 0 ≤ |σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) * lowConst φ₀ *
              taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀) := by positivity
          calc |σ' - σ| * ((2 * n + 1) * solTime φ₀ ^ n / solTime φ₀) *
                (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n)
              = (2 * n + 1) * (|σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) *
                  lowConst φ₀ * taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀)) := by ring
            _ ≤ ((2 * n + 1) * (baseY φ₀ r m + 1)) * (|σ' - σ| *
                  (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m) * lowConst φ₀ * taylorRho φ₀ ^ n *
                    solTime φ₀ ^ n / solTime φ₀)) := mul_le_mul_of_nonneg_right hY1 this
            _ = _ := by ring
  have hsumb : Summable (fun n : ℕ => |σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^
      (r + m + 1) * lowConst φ₀ * taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀)) :=
    ((summable_lip φ₀ m r).div_const _).mul_left _
  have hnorm : Summable (fun n => ‖(σ' ^ n - σ ^ n) • D n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((hsn hσ2').add (hsn hσ2))
    rw [sub_smul]; exact norm_sub_le _ _
  calc ‖x‖ ^ m * ‖∑' n, (σ' ^ n - σ ^ n) • D n‖
      ≤ ‖x‖ ^ m * ∑' n, ‖(σ' ^ n - σ ^ n) • D n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by positivity)
    _ = ∑' n, ‖x‖ ^ m * ‖(σ' ^ n - σ ^ n) • D n‖ := tsum_mul_left.symm
    _ ≤ ∑' n : ℕ, |σ' - σ| * (((2 * n + 1) * (baseY φ₀ r m + 1)) ^ (r + m + 1) * lowConst φ₀ *
          taylorRho φ₀ ^ n * solTime φ₀ ^ n / solTime φ₀) :=
        (hnorm.mul_left _).tsum_le_tsum hb hsumb
    _ = lipConst φ₀ m r * |σ' - σ| := by
        rw [tsum_mul_left]
        simp_rw [div_eq_mul_inv]
        rw [tsum_mul_right]; unfold lipConst; rw [div_eq_mul_inv]; ring

theorem continuous_taylorSol : Continuous (taylorSol hd φ₀) := by
  rw [continuous_iff_continuousAt]
  intro τ
  refine ((schwartz_withSeminorms ℝ (Mom d) ℝ).tendsto_nhds _ _).mpr fun i ε hε => ?_
  have hL : 0 ≤ lipConst φ₀ i.1 i.2 := by
    unfold lipConst
    exact div_nonneg (tsum_nonneg fun n => by
      have := baseY_nonneg φ₀ i.2 i.1; have := (lowConst_pos φ₀).le
      have := taylorRho_nonneg φ₀; have := (solTime_pos φ₀).le; positivity) (solTime_pos φ₀).le
  have hcont : Tendsto (fun τ' => lipConst φ₀ i.1 i.2 * |τ' - τ|) (𝓝 τ) (𝓝 0) := by
    have : Tendsto (fun τ' => lipConst φ₀ i.1 i.2 * |τ' - τ|) (𝓝 τ)
        (𝓝 (lipConst φ₀ i.1 i.2 * |τ - τ|)) :=
      tendsto_const_nhds.mul ((continuous_id.sub continuous_const).abs.tendsto τ)
    simpa using this
  filter_upwards [hcont.eventually (gt_mem_nhds hε)] with τ' hτ'
  calc (schwartzSeminormFamily ℝ (Mom d) ℝ i) (taylorSol hd φ₀ τ' - taylorSol hd φ₀ τ)
      ≤ lipConst φ₀ i.1 i.2 * |clampT φ₀ τ' - clampT φ₀ τ| :=
        seminorm_taylorSchwartz_sub_le hd φ₀ _ _ i.1 i.2
    _ ≤ lipConst φ₀ i.1 i.2 * |τ' - τ| :=
        mul_le_mul_of_nonneg_left (abs_clampT_sub_le φ₀ τ τ') hL
    _ < ε := hτ'

/-! ### The time derivative -/

theorem summable_coeff_pointwise {σ : ℝ} (hσ : |σ| ≤ 2 * solTime φ₀) (k : Mom d) :
    Summable (fun n => σ ^ n * taylorCoeff hd φ₀ n k) := by
  refine Summable.of_norm_bounded (summable_taylor_bound φ₀ hσ 0 0) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h := abs_coeff_le hd φ₀ n k
  have hw : (1 + ‖k‖) ^ (-(2 * (d : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg k]) (by linarith)
  have hX := (lowConst_pos φ₀).le; have hρ := taylorRho_nonneg φ₀
  calc |σ| ^ n * |taylorCoeff hd φ₀ n k| ≤ |σ| ^ n * (lowConst φ₀ * taylorRho φ₀ ^ n) := by
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
        exact mul_le_of_le_one_right (by positivity) hw
    _ = _ := by simp; ring

theorem hasDerivAt_taylorPointwise (k : Mom d) {σ : ℝ}
    (hσ : σ ∈ Ioo (-(2 * solTime φ₀)) (2 * solTime φ₀)) :
    HasDerivAt (fun s => ∑' n, s ^ n * taylorCoeff hd φ₀ n k)
      (∑' n : ℕ, (n : ℝ) * σ ^ (n - 1) * taylorCoeff hd φ₀ n k) σ := by
  have hT := solTime_pos φ₀
  have hX := (lowConst_pos φ₀).le; have hρ := taylorRho_nonneg φ₀
  set u : ℕ → ℝ := fun n => (n : ℝ) * (2 * solTime φ₀) ^ (n - 1) * (lowConst φ₀ * taylorRho φ₀ ^ n)
  have hu : Summable u := by
    have hq : 2 * solTime φ₀ * taylorRho φ₀ ≤ 1 / 2 := by have := solTime_mul_rho φ₀; linarith
    have hs := (summable_two_mul_add_one_pow_mul_geometric 1 (q := 2 * solTime φ₀ * taylorRho φ₀)
      (by positivity) (by linarith)).mul_left (lowConst φ₀ / (2 * solTime φ₀))
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    have h1 := nat_mul_pow_pred_le (by positivity : 0 < 2 * solTime φ₀) n
    calc u n = ((n : ℝ) * (2 * solTime φ₀) ^ (n - 1)) * (lowConst φ₀ * taylorRho φ₀ ^ n) := rfl
      _ ≤ ((2 * n + 1) * (2 * solTime φ₀) ^ n / (2 * solTime φ₀)) *
          (lowConst φ₀ * taylorRho φ₀ ^ n) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by push_cast; simp only [mul_pow, pow_one]; field_simp
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Ioo (-(2 * solTime φ₀)) (2 * solTime φ₀) →
      ‖(n : ℝ) * y ^ (n - 1) * taylorCoeff hd φ₀ n k‖ ≤ u n := by
    intro n y hy
    have hy' : |y| ≤ 2 * solTime φ₀ := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    have h := abs_coeff_le hd φ₀ n k
    have hw : (1 + ‖k‖) ^ (-(2 * (d : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg k]) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have h2 : |taylorCoeff hd φ₀ n k| ≤ lowConst φ₀ * taylorRho φ₀ ^ n :=
      h.trans (mul_le_of_le_one_right (by positivity) hw)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy' _)
      (by positivity)) h2 (abs_nonneg _) (by positivity)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).mul_const _) hbound hσ
    (summable_coeff_pointwise hd φ₀ (abs_le.mpr ⟨hσ.1.le, hσ.2.le⟩) k) hσ

theorem tsum_deriv_shift {σ : ℝ} (hσ : |σ| < 2 * solTime φ₀) (k : Mom d) :
    ∑' n : ℕ, (n : ℝ) * σ ^ (n - 1) * taylorCoeff hd φ₀ n k =
      ∑' m : ℕ, ((m : ℝ) + 1) * σ ^ m * taylorCoeff hd φ₀ (m + 1) k := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * σ ^ (n - 1) * taylorCoeff hd φ₀ n k) := by
    have h := (hasDerivAt_taylorPointwise hd φ₀ k (σ := σ) (abs_lt.mp hσ))
    -- summability from the domination used there
    have hT := solTime_pos φ₀
    have hX := (lowConst_pos φ₀).le; have hρ := taylorRho_nonneg φ₀
    have hq : 2 * solTime φ₀ * taylorRho φ₀ ≤ 1 / 2 := by have := solTime_mul_rho φ₀; linarith
    have hsg := (summable_two_mul_add_one_pow_mul_geometric 1 (q := 2 * solTime φ₀ * taylorRho φ₀)
      (by positivity) (by linarith)).mul_left (lowConst φ₀ / (2 * solTime φ₀))
    refine Summable.of_norm_bounded hsg (fun n => ?_)
    have hw : (1 + ‖k‖) ^ (-(2 * (d : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg k]) (by linarith)
    have h2 : |taylorCoeff hd φ₀ n k| ≤ lowConst φ₀ * taylorRho φ₀ ^ n :=
      (abs_coeff_le hd φ₀ n k).trans (mul_le_of_le_one_right (by positivity) hw)
    have h1 := nat_mul_pow_pred_le (by positivity : 0 < 2 * solTime φ₀) n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    calc (n : ℝ) * |σ| ^ (n - 1) * |taylorCoeff hd φ₀ n k|
        ≤ ((n : ℝ) * (2 * solTime φ₀) ^ (n - 1)) * (lowConst φ₀ * taylorRho φ₀ ^ n) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hσ.le _)
            (by positivity)) h2 (abs_nonneg _) (by positivity)
      _ ≤ ((2 * n + 1) * (2 * solTime φ₀) ^ n / (2 * solTime φ₀)) *
          (lowConst φ₀ * taylorRho φ₀ ^ n) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by push_cast; simp only [mul_pow, pow_one]; field_simp
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]

/-! ### The Cauchy product: `𝒦(S, S, S) = Σ (m+1) σᵐ aₘ₊₁` -/

/-- The weighted-sup bound `X₀ (ρ|σ|)ⁿ` of the term `σⁿ aₙ`. -/
@[expose] noncomputable def termConst (σ : ℝ) (n : ℕ) : ℝ :=
  lowConst φ₀ * (taylorRho φ₀ * |σ|) ^ n

theorem termConst_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ termConst φ₀ σ n := by
  have := (lowConst_pos φ₀).le; have := taylorRho_nonneg φ₀; unfold termConst; positivity

theorem rho_abs_le {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) : taylorRho φ₀ * |σ| ≤ 1 / 4 := by
  have := solTime_mul_rho φ₀; have hρ := taylorRho_nonneg φ₀
  calc taylorRho φ₀ * |σ| ≤ taylorRho φ₀ * solTime φ₀ := mul_le_mul_of_nonneg_left hσ hρ
    _ ≤ 1 / 4 := by linarith

theorem summable_termConst {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) : Summable (termConst φ₀ σ) := by
  have h := rho_abs_le φ₀ hσ
  exact (summable_geometric_of_lt_one (by have := taylorRho_nonneg φ₀; positivity)
    (by linarith)).mul_left _

theorem decayBound_taylorTerm (σ : ℝ) (n : ℕ) :
    DecayBound (termConst φ₀ σ n) (2 * d + 1) (taylorTerm hd φ₀ σ n) := by
  intro y
  simp only [taylorTerm, smul_apply, smul_eq_mul, abs_mul, abs_pow]
  have h := abs_coeff_le hd φ₀ n y
  calc |σ| ^ n * |taylorCoeff hd φ₀ n y|
      ≤ |σ| ^ n * (lowConst φ₀ * taylorRho φ₀ ^ n * (1 + ‖y‖) ^ (-(2 * (d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = termConst φ₀ σ n * (1 + ‖y‖) ^ (-(2 * (d : ℝ) + 1)) := by
        unfold termConst; rw [mul_pow]; ring

theorem decayBound_taylorSchwartz {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) :
    DecayBound (∑' n, termConst φ₀ σ n) (2 * d + 1) (taylorSchwartz hd φ₀ hσ) := by
  have := DecayBound.of_tsum (decayBound_taylorTerm hd φ₀ σ) (summable_termConst φ₀ hσ)
    (F := taylorSchwartz hd φ₀ hσ) (fun y => rfl) 0
  simpa using this

/-- `g ↦ 𝒦(g, b, c)(k)`, `g ↦ 𝒦(a, g, c)(k)`, `g ↦ 𝒦(a, b, g)(k)` as additive maps on `𝓢`. -/
@[expose] noncomputable def slotOne (b c : 𝓢(Mom d, ℝ)) (k : Mom d) : 𝓢(Mom d, ℝ) →+ ℝ where
  toFun g := collisionOp g b c k
  map_zero' := by simpa using collisionOp_smul_left (0 : ℝ) (0 : 𝓢(Mom d, ℝ)) b c k
  map_add' g g' := collisionOp_add_left hd g g' b c k

@[expose] noncomputable def slotTwo (a c : 𝓢(Mom d, ℝ)) (k : Mom d) : 𝓢(Mom d, ℝ) →+ ℝ where
  toFun g := collisionOp a g c k
  map_zero' := by simpa using collisionOp_smul_mid (0 : ℝ) (0 : 𝓢(Mom d, ℝ)) a c k
  map_add' g g' := collisionOp_add_mid hd a g g' c k

@[expose] noncomputable def slotThree (a b : 𝓢(Mom d, ℝ)) (k : Mom d) : 𝓢(Mom d, ℝ) →+ ℝ where
  toFun g := collisionOp a b g k
  map_zero' := by simpa using collisionOp_smul_right (0 : ℝ) (0 : 𝓢(Mom d, ℝ)) a b k
  map_add' g g' := collisionOp_add_right hd a b g g' k

/-- Expansion of one slot of `𝒦` along the Taylor series. -/
theorem slot_expand {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (L : 𝓢(Mom d, ℝ) →+ ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hL : ∀ (g : 𝓢(Mom d, ℝ)) (C : ℝ), DecayBound C (2 * d + 1) (⇑g) → |L g| ≤ K * C) :
    L (taylorSchwartz hd φ₀ hσ) = ∑' n, L (taylorTerm hd φ₀ σ n) :=
  (tsum_of_bounded_additive L hK hL (decayBound_taylorTerm hd φ₀ σ) (summable_termConst φ₀ hσ)
    (fun _ => rfl)).1

theorem cauchy_step1 {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (k : Mom d) :
    collisionOp (taylorSchwartz hd φ₀ hσ) (taylorSchwartz hd φ₀ hσ) (taylorSchwartz hd φ₀ hσ) k =
      ∑' n₁, ∑' n₂, ∑' n₃, collisionOp (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ n₂)
        (taylorTerm hd φ₀ σ n₃) k := by
  set S := taylorSchwartz hd φ₀ hσ
  have hS := decayBound_taylorSchwartz hd φ₀ hσ
  have hCS : 0 ≤ ∑' n, termConst φ₀ σ n := tsum_nonneg (termConst_nonneg φ₀ σ)
  have hK := opConst_nonneg d
  have e1 := slot_expand hd φ₀ hσ (slotOne hd S S k) (K := opConst d *
      ((∑' n, termConst φ₀ σ n) * ∑' n, termConst φ₀ σ n)) (by positivity)
    (fun g C hg => (abs_collisionOp_le_sup hd hg hS hS k).trans_eq (by ring))
  refine e1.trans (tsum_congr fun n₁ => ?_)
  have hC1 := termConst_nonneg φ₀ σ n₁
  have e2 := slot_expand hd φ₀ hσ (slotTwo hd (taylorTerm hd φ₀ σ n₁) S k)
    (K := opConst d * (termConst φ₀ σ n₁ * ∑' n, termConst φ₀ σ n)) (by positivity)
    (fun g C hg => (abs_collisionOp_le_sup hd (decayBound_taylorTerm hd φ₀ σ n₁) hg hS
      k).trans_eq (by ring))
  refine e2.trans (tsum_congr fun n₂ => ?_)
  have hC2 := termConst_nonneg φ₀ σ n₂
  exact slot_expand hd φ₀ hσ (slotThree hd (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ n₂) k)
    (K := opConst d * (termConst φ₀ σ n₁ * termConst φ₀ σ n₂)) (by positivity)
    (fun g C hg => (abs_collisionOp_le_sup hd (decayBound_taylorTerm hd φ₀ σ n₁)
      (decayBound_taylorTerm hd φ₀ σ n₂) hg k).trans_eq (by ring))

theorem abs_collisionOp_taylorTerm_le (σ : ℝ) (k : Mom d) (n₁ n₂ n₃ : ℕ) :
    |collisionOp (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ n₂) (taylorTerm hd φ₀ σ n₃) k| ≤
      opConst d * (termConst φ₀ σ n₁ * termConst φ₀ σ n₂ * termConst φ₀ σ n₃) :=
  abs_collisionOp_le_sup hd (decayBound_taylorTerm hd φ₀ σ n₁) (decayBound_taylorTerm hd φ₀ σ n₂)
    (decayBound_taylorTerm hd φ₀ σ n₃) k

theorem summable_termConst_prod {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) :
    Summable (fun p : ℕ × ℕ => termConst φ₀ σ p.1 * termConst φ₀ σ p.2) := by
  have h := summable_termConst φ₀ hσ
  have hn : Summable (fun n => ‖termConst φ₀ σ n‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (termConst_nonneg φ₀ σ _)] using h
  exact summable_mul_of_summable_norm (R := ℝ) hn hn

theorem termConst_mul_antidiagonal (σ : ℝ) {l : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal l) :
    termConst φ₀ σ p.1 * termConst φ₀ σ p.2 = lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ l := by
  have := mem_antidiagonal.mp hp
  unfold termConst; rw [← this, pow_add]; ring

theorem summable_cauchy_outer {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (k : Mom d) :
    Summable (fun p : ℕ × ℕ => ∑ r ∈ antidiagonal p.2, collisionOp (taylorTerm hd φ₀ σ p.1)
      (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k) := by
  have hq := rho_abs_le φ₀ hσ
  have hq0 : 0 ≤ taylorRho φ₀ * |σ| := by have := taylorRho_nonneg φ₀; positivity
  have hg : Summable (fun l : ℕ => ((l : ℝ) + 1) * (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ l)) := by
    have := (summable_two_mul_add_one_pow_mul_geometric 1 hq0 (by linarith)).mul_left
      (lowConst φ₀ ^ 2)
    refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) this
    push_cast
    have h0 : 0 ≤ lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ l := by positivity
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  have hprod : Summable (fun p : ℕ × ℕ => termConst φ₀ σ p.1 *
      (((p.2 : ℝ) + 1) * (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ p.2))) := by
    refine summable_mul_of_summable_norm (R := ℝ) (f := termConst φ₀ σ)
      (g := fun l : ℕ => ((l : ℝ) + 1) * (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ l)) ?_ ?_
    · simpa [Real.norm_eq_abs, abs_of_nonneg (termConst_nonneg φ₀ σ _)] using
        summable_termConst φ₀ hσ
    · refine hg.congr fun l => ?_
      have hρ := taylorRho_nonneg φ₀
      have h0 : 0 ≤ ((l : ℝ) + 1) * (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ l) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine Summable.of_norm_bounded (hprod.mul_left (opConst d)) (fun p => ?_)
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ antidiagonal p.2, |collisionOp (taylorTerm hd φ₀ σ p.1) (taylorTerm hd φ₀ σ r.1)
        (taylorTerm hd φ₀ σ r.2) k|
      ≤ ∑ r ∈ antidiagonal p.2, opConst d * (termConst φ₀ σ p.1 * termConst φ₀ σ r.1 *
          termConst φ₀ σ r.2) :=
        Finset.sum_le_sum fun r _ => abs_collisionOp_taylorTerm_le hd φ₀ σ k _ _ _
    _ = ∑ r ∈ antidiagonal p.2, opConst d * (termConst φ₀ σ p.1 *
          (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ p.2)) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [mul_assoc (termConst φ₀ σ p.1), termConst_mul_antidiagonal φ₀ σ hr]
    _ = opConst d * (termConst φ₀ σ p.1 *
          (((p.2 : ℝ) + 1) * (lowConst φ₀ ^ 2 * (taylorRho φ₀ * |σ|) ^ p.2))) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring

theorem cauchy_step2 {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (k : Mom d) :
    ∑' n₁, ∑' n₂, ∑' n₃, collisionOp (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ n₂)
        (taylorTerm hd φ₀ σ n₃) k =
      ∑' m, ∑ p ∈ antidiagonal m, ∑ r ∈ antidiagonal p.2, collisionOp (taylorTerm hd φ₀ σ p.1)
        (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k := by
  have hinner : ∀ n₁, ∑' n₂, ∑' n₃, collisionOp (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ n₂)
      (taylorTerm hd φ₀ σ n₃) k = ∑' l, ∑ r ∈ antidiagonal l, collisionOp (taylorTerm hd φ₀ σ n₁)
        (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k := by
    intro n₁
    refine tsum_tsum_eq_tsum_sum_antidiagonal (G := fun r : ℕ × ℕ =>
      collisionOp (taylorTerm hd φ₀ σ n₁) (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k) ?_
    refine Summable.of_norm_bounded (((summable_termConst_prod φ₀ hσ).mul_left
      (opConst d * termConst φ₀ σ n₁))) (fun r => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_collisionOp_taylorTerm_le hd φ₀ σ k n₁ r.1 r.2).trans_eq (by ring)
  simp_rw [hinner]
  exact tsum_tsum_eq_tsum_sum_antidiagonal (G := fun p : ℕ × ℕ => ∑ r ∈ antidiagonal p.2,
    collisionOp (taylorTerm hd φ₀ σ p.1) (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k)
    (summable_cauchy_outer hd φ₀ hσ k)

theorem cauchy_step3 (σ : ℝ) (k : Mom d) (m : ℕ) :
    ∑ p ∈ antidiagonal m, ∑ r ∈ antidiagonal p.2, collisionOp (taylorTerm hd φ₀ σ p.1)
        (taylorTerm hd φ₀ σ r.1) (taylorTerm hd φ₀ σ r.2) k =
      ((m : ℝ) + 1) * σ ^ m * taylorCoeff hd φ₀ (m + 1) k := by
  rw [taylorCoeff_succ, smul_apply, _root_.sum_apply, smul_eq_mul]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [show ∀ X : ℝ, ((m : ℝ) + 1) * σ ^ m * (((m : ℝ) + 1)⁻¹ * X) = σ ^ m * X from
    fun X => by field_simp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [_root_.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h1 := mem_antidiagonal.mp hp; have h2 := mem_antidiagonal.mp hr
  simp only [taylorTerm]
  rw [collisionOp_smul_left, collisionOp_smul_mid, collisionOp_smul_right,
    coe_collisionOpSchwartz, ← h1, ← h2, pow_add, pow_add]
  ring

theorem collisionOp_taylorSchwartz {σ : ℝ} (hσ : |σ| ≤ solTime φ₀) (k : Mom d) :
    collisionOp (taylorSchwartz hd φ₀ hσ) (taylorSchwartz hd φ₀ hσ) (taylorSchwartz hd φ₀ hσ) k =
      ∑' m : ℕ, ((m : ℝ) + 1) * σ ^ m * taylorCoeff hd φ₀ (m + 1) k := by
  rw [cauchy_step1 hd φ₀ hσ k, cauchy_step2 hd φ₀ hσ k]
  exact tsum_congr fun m => cauchy_step3 hd φ₀ σ k m

/-! ### The solution -/

theorem taylorSol_eq {τ : ℝ} (hτ : |τ| ≤ solTime φ₀) (h0 : 0 ≤ τ) :
    taylorSol hd φ₀ τ = taylorSchwartz hd φ₀ hτ := by
  ext y
  rw [taylorSol_apply, taylorSchwartz_apply,
    clampT_of_mem φ₀ ⟨h0, (abs_le.mp hτ).2⟩]

/-- **Local existence**: the power series is a Schwartz-class solution of (WKE) on `[0, T]`. -/
theorem isWKESolution_taylorSol :
    IsWKESolution φ₀ (solTime φ₀) (taylorSol hd φ₀) := by
  have hT := solTime_pos φ₀
  refine ⟨(continuous_taylorSol hd φ₀).continuousOn, taylorSol_zero hd φ₀, fun τ hτ k => ?_⟩
  have hτ' : |τ| ≤ solTime φ₀ := by rw [abs_of_nonneg hτ.1]; exact hτ.2
  have hmem : τ ∈ Ioo (-(2 * solTime φ₀)) (2 * solTime φ₀) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hd' := (hasDerivAt_taylorPointwise hd φ₀ k hmem).hasDerivWithinAt (s := Icc 0 (solTime φ₀))
  have hval : ∑' n : ℕ, (n : ℝ) * τ ^ (n - 1) * taylorCoeff hd φ₀ n k =
      collisionOp (taylorSol hd φ₀ τ) (taylorSol hd φ₀ τ) (taylorSol hd φ₀ τ) k := by
    rw [tsum_deriv_shift hd φ₀ (by linarith [abs_nonneg τ]) k, taylorSol_eq hd φ₀ hτ' hτ.1,
      collisionOp_taylorSchwartz]
  rw [← hval]
  refine hd'.congr_of_mem (fun s hs => ?_) hτ
  rw [taylorSol_apply, clampT_of_mem φ₀ hs]

/-- **Local existence of Schwartz solutions** (TARGET Prop `wkelwp`, existence part). -/
theorem exists_isWKESolution (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ)) :
    ∃ T > 0, ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φ₀ T φ :=
  ⟨solTime φ₀, solTime_pos φ₀, taylorSol hd φ₀, isWKESolution_taylorSol hd φ₀⟩

end Solution

/-! ### `τ_max`: TARGET Prop `wkelwp` conjuncts 1–2 -/

/-- `0 < τ_max` (TARGET Prop `wkelwp`, L598). -/
theorem tauMax_pos (hd : 2 ≤ d) (φin : 𝓢(Mom d, ℝ)) : 0 < tauMax φin := by
  obtain ⟨T, hT, φ, hφ⟩ := exists_isWKESolution hd φin
  exact (ENNReal.ofReal_pos.mpr hT).trans_le (ofReal_le_tauMax hT hφ)

/-- **`wkelwp` conjunct 1** (TARGET L598–L601): for `τ★ > 0`, `τ★ < τ_max` iff (WKE) has a
Schwartz-class solution on the closed interval `[0, τ★]`. The `←` direction extends a solution
on `[0, τ★]` past `τ★` by local existence from the data `φ(τ★)` and gluing. -/
theorem lt_tauMax_iff (hd : 2 ≤ d) (φin : 𝓢(Mom d, ℝ)) {τstar : ℝ} (hτ : 0 < τstar) :
    ENNReal.ofReal τstar < tauMax φin ↔ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ := by
  refine ⟨exists_isWKESolution_of_lt_tauMax, fun ⟨φ, hφ⟩ => ?_⟩
  obtain ⟨ε, hε, ψ, hψ⟩ := exists_isWKESolution hd (φ τstar)
  have hglue := isWKESolution_glue hτ.le hε.le hφ hψ
  refine lt_of_lt_of_le ?_ (ofReal_le_tauMax (by linarith) hglue)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

/-- **TARGET Prop `wkelwp`, conjuncts 1–2, exactly as in the frozen anchor** (existence of `τ_max`
with `0 < τ_max`, the characterization of `τ_max`, and uniqueness), for `d ≥ 2`. -/
theorem wkelwp_conj12 (d : ℕ) (hd : 2 ≤ d) (φin : 𝓢(Mom d, ℝ)) :
    ∃ τmax : ℝ≥0∞, 0 < τmax ∧
      (∀ τstar > (0 : ℝ),
        (ENNReal.ofReal τstar < τmax ↔ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ)) ∧
      (∀ τstar > (0 : ℝ), ∀ φ ψ : ℝ → 𝓢(Mom d, ℝ),
        IsWKESolution φin τstar φ → IsWKESolution φin τstar ψ → ∀ τ ∈ Icc 0 τstar, φ τ = ψ τ) :=
  ⟨tauMax φin, tauMax_pos hd φin, fun _ hτ => lt_tauMax_iff hd φin hτ,
    fun _ _ _ _ hφ hψ => isWKESolution_unique hd hφ hψ⟩

end WaveTurbulence.WKE

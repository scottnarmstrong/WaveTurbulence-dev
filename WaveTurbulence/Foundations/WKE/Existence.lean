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

end Solution

end WaveTurbulence.WKE

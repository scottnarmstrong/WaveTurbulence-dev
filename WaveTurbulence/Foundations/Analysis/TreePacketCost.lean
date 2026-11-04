/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreeResonanceWeights

/-!
# Exponential control of the common packet cost

A full ternary tree with `n` branches has `2n+1` leaves. Counting the
convolution and cutoff losses directly gives an exponential bound in `n`.
-/

public section

open scoped ENNReal

namespace WaveTurbulence.Analysis.IntegrationTree

/-- A real common bound for a leaf cost, a branch cost and one. -/
@[expose] noncomputable def packetCostBase (χ : ℝ → ℂ) : ℝ :=
  1 + cutoffFourierConstant χ + cutoffKernelConstant χ * (12 * Real.pi) * (4 * Real.pi) ^ 2

theorem one_le_packetCostBase (χ : ℝ → ℂ) : 1 ≤ packetCostBase χ := by
  unfold packetCostBase
  have := cutoffFourierConstant_nonneg χ
  have hA : 0 ≤ cutoffKernelConstant χ * (12 * Real.pi) * (4 * Real.pi) ^ 2 :=
    mul_nonneg (mul_nonneg (cutoffKernelConstant_nonneg χ) (by positivity)) (sq_nonneg _)
  linarith

private theorem branchingCost_le_base (χ : ℝ → ℂ) : branchingCost χ ≤ ENNReal.ofReal (packetCostBase χ) := by
  have heq : branchingCost χ =
      ENNReal.ofReal (cutoffKernelConstant χ * (12 * Real.pi) * (4 * Real.pi) ^ 2) := by
    unfold branchingCost
    rw [ENNReal.ofReal_mul (mul_nonneg (cutoffKernelConstant_nonneg χ) (by positivity)),
      ENNReal.ofReal_mul (cutoffKernelConstant_nonneg χ),
      ENNReal.ofReal_pow (by positivity)]
    ring
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  unfold packetCostBase
  linarith [cutoffFourierConstant_nonneg χ]

/-- A degree-three cost per branch, plus one initial leaf cost. -/
theorem packetCost_le_base_pow (χ : ℝ → ℂ) (T : IntegrationTree) :
    T.packetCost χ ≤ ENNReal.ofReal (packetCostBase χ) ^ (3 * T.branchCount + 1) := by
  induction T with
  | leaf =>
      simp only [packetCost, branchCount, mul_zero, zero_add, pow_one]
      apply ENNReal.ofReal_le_ofReal
      unfold packetCostBase
      have hA : 0 ≤ cutoffKernelConstant χ * (12 * Real.pi) * (4 * Real.pi) ^ 2 :=
        mul_nonneg (mul_nonneg (cutoffKernelConstant_nonneg χ) (by positivity)) (sq_nonneg _)
      linarith
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      have hh := mul_le_mul' (branchingCost_le_base χ) (mul_le_mul' (mul_le_mul' hl hm) hr)
      change branchingCost χ * ((l.packetCost χ * m.packetCost χ) * r.packetCost χ) ≤ _
      refine hh.trans_eq ?_
      rw [← pow_add, ← pow_add, ← pow_succ']
      congr 1
      simp only [branchCount]
      omega

/-- A real exponential constant, including the final Cauchy mass. -/
@[expose] noncomputable def treeIntegralConstant (χ : ℝ → ℂ) : ℝ :=
  max 1 Real.pi * packetCostBase χ ^ 4

/-- For a nontrivial tree, all common analytic losses fit into `C^n`. -/
theorem packetCost_mul_pi_le_pow (χ : ℝ → ℂ) (T : IntegrationTree) (hn : 0 < T.branchCount) :
    T.packetCost χ * ENNReal.ofReal Real.pi ≤
      ENNReal.ofReal (treeIntegralConstant χ) ^ T.branchCount := by
  have hD : 1 ≤ ENNReal.ofReal (packetCostBase χ) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (one_le_packetCostBase χ)
  have hP : 1 ≤ ENNReal.ofReal (max 1 Real.pi) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) Real.pi)
  have hpi : ENNReal.ofReal Real.pi ≤ ENNReal.ofReal (max 1 Real.pi) ^ T.branchCount :=
    (ENNReal.ofReal_le_ofReal (le_max_right (1 : ℝ) Real.pi)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hP hn)
  calc
    _ ≤ ENNReal.ofReal (packetCostBase χ) ^ (3 * T.branchCount + 1) *
        ENNReal.ofReal (max 1 Real.pi) ^ T.branchCount := mul_le_mul' (packetCost_le_base_pow χ T) hpi
    _ ≤ ENNReal.ofReal (packetCostBase χ) ^ (4 * T.branchCount) *
        ENNReal.ofReal (max 1 Real.pi) ^ T.branchCount :=
      mul_le_mul' (pow_le_pow_right₀ hD (by omega)) le_rfl
    _ = _ := by
      rw [treeIntegralConstant, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by linarith [one_le_packetCostBase χ]), mul_pow, ← pow_mul]
      exact mul_comm _ _

end WaveTurbulence.Analysis.IntegrationTree

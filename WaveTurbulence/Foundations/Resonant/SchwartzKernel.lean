/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.Integral
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Local uniform decay for Schwartz test kernels

The three-momentum test function is evaluated at
`(k+ℓ, k+ℓ+x, k+x)`. Schwartz decay controls both free momenta. On a unit
neighborhood of `k₀`, a Peetre inequality supplies fixed polynomial profiles,
as required by dominated Fréchet differentiation.
-/

public section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace WaveTurbulence.Resonant

/-- The three momentum variables of a collision test function. -/
abbrev MomTriple (d : ℕ) := Mom d × Mom d × Mom d

/-- The parametrization shared by the resonant integral and the frozen collision operator. -/
@[expose] def triplePoint {d : ℕ} (k ℓ x : Mom d) : MomTriple d :=
  (k + ℓ, k + ℓ + x, k + x)

/-- The derivative of the three-momentum parametrization with respect to `k`. -/
@[expose] noncomputable def diagonalCLM (d : ℕ) : Mom d →L[ℝ] MomTriple d :=
  (ContinuousLinearMap.id ℝ (Mom d)).prod
    ((ContinuousLinearMap.id ℝ (Mom d)).prod (ContinuousLinearMap.id ℝ (Mom d)))

/-- Schwartz decay with a real exponent, for arbitrary normed domain and codomain. -/
theorem exists_polynomial_decay_schwartz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : 𝓢(E, F)) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
  set n : ℕ := ⌈N⌉₊
  set S : ℝ := 2 ^ n * (Finset.Iic (n, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨S, hS, fun y => ?_⟩
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0)) le_rfl le_rfl f y
  rw [norm_iteratedFDeriv_zero] at hb
  have hp : 0 < 1 + ‖y‖ := by positivity
  have h1 : ‖f y‖ ≤ S * ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith [mul_comm ((1 + ‖y‖) ^ n) ‖f y‖]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hS)
  rw [← Real.rpow_natCast, ← Real.rpow_neg hp.le]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (by linarith [Nat.le_ceil N])

/-- A normed-group Peetre inequality on a unit neighborhood. -/
theorem polynomial_profile_le_of_dist
    {E : Type*} [NormedAddCommGroup E] {y z : E} (h : ‖z - y‖ ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) :
    (1 + ‖z‖) ^ (-M) ≤ 2 ^ M * (1 + ‖y‖) ^ (-M) := by
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hz : 0 < 1 + ‖z‖ := by positivity
  have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
  rw [norm_sub_rev] at h2
  have hk : 1 + ‖y‖ ≤ 2 * (1 + ‖z‖) := by linarith [norm_nonneg z]
  rw [Real.rpow_neg hz.le, Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + ‖z‖) ^ M)⁻¹ * (1 + ‖y‖) ^ M
      ≤ ((1 + ‖z‖) ^ M)⁻¹ * (2 * (1 + ‖z‖)) ^ M :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le hk hM) (by positivity)
    _ = 2 ^ M := by
      rw [Real.mul_rpow (by norm_num) hz.le]
      field_simp

/-- Joint decay controls both free momenta in the resonance parametrization. -/
theorem norm_triplePoint_decay
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] {f : MomTriple d → E} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-(2 * M))) (k ℓ x : Mom d) :
    ‖f (triplePoint k ℓ x)‖ ≤
      C * (1 + ‖k + ℓ‖) ^ (-M) * (1 + ‖k + x‖) ^ (-M) := by
  have hfirst : ‖k + ℓ‖ ≤ ‖triplePoint k ℓ x‖ := norm_fst_le (triplePoint k ℓ x)
  have hthird : ‖k + x‖ ≤ ‖triplePoint k ℓ x‖ := (norm_snd_le (k + ℓ + x, k + x)).trans (norm_snd_le (triplePoint k ℓ x))
  have hp : 0 < 1 + ‖triplePoint k ℓ x‖ := by positivity
  have h1 : (1 + ‖triplePoint k ℓ x‖) ^ (-M) ≤ (1 + ‖k + ℓ‖) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (add_le_add (le_refl (1 : ℝ)) hfirst) (by linarith)
  have h3 : (1 + ‖triplePoint k ℓ x‖) ^ (-M) ≤ (1 + ‖k + x‖) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (add_le_add (le_refl (1 : ℝ)) hthird) (by linarith)
  have he : -(2 * M) = -M + -M := by ring
  calc ‖f (triplePoint k ℓ x)‖ ≤ C * (1 + ‖triplePoint k ℓ x‖) ^ (-(2 * M)) := hb _
    _ = C * ((1 + ‖triplePoint k ℓ x‖) ^ (-M) * (1 + ‖triplePoint k ℓ x‖) ^ (-M)) := by
      rw [he, Real.rpow_add hp]
    _ ≤ C * ((1 + ‖k + ℓ‖) ^ (-M) * (1 + ‖k + x‖) ^ (-M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h3 (by positivity) (by positivity)) hC
    _ = _ := by ring

/-- Fixed decay profiles on a unit neighborhood of the external momentum. -/
theorem norm_triplePoint_decay_local
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] {f : MomTriple d → E} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-(2 * M)))
    {k k₀ : Mom d} (hk : ‖k - k₀‖ ≤ 1) (ℓ x : Mom d) :
    ‖f (triplePoint k ℓ x)‖ ≤
      (C * (2 ^ M) ^ 2) * (1 + ‖k₀ + ℓ‖) ^ (-M) * (1 + ‖k₀ + x‖) ^ (-M) := by
  have hdist : ∀ y : Mom d, ‖(k + y) - (k₀ + y)‖ ≤ 1 := by
    intro y
    have he : (k + y) - (k₀ + y) = k - k₀ := by abel
    rw [he]
    exact hk
  have h1 := polynomial_profile_le_of_dist (hdist ℓ) hM
  have h3 := polynomial_profile_le_of_dist (hdist x) hM
  refine (norm_triplePoint_decay hC hM hb k ℓ x).trans ?_
  calc C * (1 + ‖k + ℓ‖) ^ (-M) * (1 + ‖k + x‖) ^ (-M)
      = C * ((1 + ‖k + ℓ‖) ^ (-M) * (1 + ‖k + x‖) ^ (-M)) := by ring
    _ ≤ C * ((2 ^ M * (1 + ‖k₀ + ℓ‖) ^ (-M)) *
        (2 ^ M * (1 + ‖k₀ + x‖) ^ (-M))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h3 (by positivity) (by positivity)) hC
    _ = _ := by ring

/-- Local delta-kernel hypotheses obtained from joint polynomial decay. -/
theorem deltaKernel_triple_of_decay
    {d : ℕ} {f : MomTriple d → ℝ} {C M : ℝ} (hd : 2 ≤ d) (hM : (d : ℝ) < M)
    (hC : 0 ≤ C) (hc : Continuous f)
    (hb : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ (-(2 * M)))
    {k k₀ : Mom d} (hk : ‖k - k₀‖ ≤ 1) :
    DeltaKernel (fun ℓ x => f (triplePoint k ℓ x))
      (fun ℓ => (C * (2 ^ M) ^ 2) * (1 + ‖k₀ + ℓ‖) ^ (-M)) (fun _ => k₀) M where
  cont := by
    apply hc.comp
    unfold triplePoint
    fun_prop
  bound ℓ x := by
    have hh : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-(2 * M)) := by
      simpa only [Real.norm_eq_abs] using hb
    simpa only [Real.norm_eq_abs] using norm_triplePoint_decay_local hC
      (le_trans (Nat.cast_nonneg d) hM.le) hh hk ℓ x
  dim := hM
  integrable := by
    simpa only [mul_left_comm _ (C * (2 ^ M) ^ 2)] using
      (integrable_inv_norm_mul_one_add_norm hd hM k₀).const_mul (C * (2 ^ M) ^ 2)

end WaveTurbulence.Resonant

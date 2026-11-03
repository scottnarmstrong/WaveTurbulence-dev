/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkClass

/-!
# Gronwall estimates for weighted `ℓ¹` sums along integral equations

* `le_mul_exp_of_le_add_integral`: the integral Gronwall inequality: a continuous nonnegative `φ`
  with `φ(t) ≤ A + K ∫₀ᵗ φ` on `[0, T]` satisfies `φ(t) ≤ A e^{Kt}`;
* `tsum_weighted_le_exp`: for families `ψₙ(t) = ψₙ(0) + ∫₀ᵗ Gₙ` with summable majorants and
  `∑ wₙ |Gₙ(t)| ≤ K ∑ wₙ |ψₙ(t)|`, the weighted sum `∑ wₙ |ψₙ(t)|` grows at most like `e^{Kt}`.

These drive uniqueness (`w = 1`, `ψ = a - b`) and persistence of regularity (truncated polynomial
weights) for the `a`-system (packet NLS goal 5).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence.NLS

/-- The integral Gronwall inequality on `[0, T]`. -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {A K T : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hφ : ContinuousOn φ (Icc 0 T)) (hφ0 : ∀ t ∈ Icc 0 T, 0 ≤ φ t)
    (h : ∀ t ∈ Icc 0 T, φ t ≤ A + K * ∫ s in (0 : ℝ)..t, φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ A * Real.exp (K * t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set ψ : ℝ → ℝ := IccExtend hT ((Icc 0 T).domRestrict φ) with hψdef
  have hψc : Continuous ψ :=
    continuous_IccExtend_iff.2 (continuousOn_iff_continuous_domRestrict.1 hφ)
  have hψφ : ∀ s ∈ Icc 0 T, ψ s = φ s := fun s hs => by
    rw [hψdef, IccExtend_of_mem hT _ hs]
    rfl
  set Ψ : ℝ → ℝ := fun u => A + K * ∫ s in (0 : ℝ)..u, ψ s with hΨdef
  have hInt : ∀ u ∈ Icc 0 T, ∫ s in (0 : ℝ)..u, ψ s = ∫ s in (0 : ℝ)..u, φ s := by
    intro u hu
    refine intervalIntegral.integral_congr fun s hs => hψφ s ?_
    rw [uIcc_of_le hu.1] at hs
    exact ⟨hs.1, hs.2.trans hu.2⟩
  have hΨφ : ∀ u ∈ Icc 0 T, φ u ≤ Ψ u := fun u hu => by
    simp only [hΨdef]
    rw [hInt u hu]
    exact h u hu
  have hΨ0 : ∀ u ∈ Icc 0 T, 0 ≤ Ψ u := fun u hu => (hφ0 u hu).trans (hΨφ u hu)
  have hderiv : ∀ u, HasDerivAt Ψ (K * ψ u) u := fun u =>
    ((hψc.integral_hasStrictDerivAt 0 u).hasDerivAt.const_mul K).const_add A
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := Ψ) (f' := fun u => K * ψ u)
    (δ := A) (K := K) (ε := 0) (a := 0) (b := T)
    (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
    (fun u _ => (hderiv u).hasDerivWithinAt)
    (by simp [hΨdef, abs_of_nonneg hA]) (fun u hu => ?_) t ht
  · rw [gronwallBound_ε0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hΨ0 t ht)] at hg
    exact (hΨφ t ht).trans hg
  · have hu' : u ∈ Icc 0 T := Ico_subset_Icc_self hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hψφ u hu',
      abs_of_nonneg (mul_nonneg hK (hφ0 u hu')), abs_of_nonneg (hΨ0 u hu'), add_zero]
    exact mul_le_mul_of_nonneg_left (hΨφ u hu') hK

variable {ι : Type*} [Countable ι]

/-- Weighted sums along integral equations grow at most exponentially. -/
theorem tsum_weighted_le_exp {ψ G : ι → ℝ → ℂ} {w : ι → ℝ} {T K : ℝ} (hK : 0 ≤ K)
    (hw : ∀ n, 0 ≤ w n) (hψ : ∀ n, ContinuousOn (ψ n) (Icc 0 T))
    (hG : ∀ n, ContinuousOn (G n) (Icc 0 T))
    (heq : ∀ n, ∀ t ∈ Icc 0 T, ψ n t = ψ n 0 + ∫ s in (0 : ℝ)..t, G n s)
    {P Q : ι → ℝ} (hP : Summable P) (hQ : Summable Q)
    (hψP : ∀ n, ∀ t ∈ Icc 0 T, w n * ‖ψ n t‖ ≤ P n)
    (hGQ : ∀ n, ∀ t ∈ Icc 0 T, w n * ‖G n t‖ ≤ Q n)
    (hbound : ∀ t ∈ Icc 0 T, ∑' n, w n * ‖G n t‖ ≤ K * ∑' n, w n * ‖ψ n t‖) :
    ∀ t ∈ Icc 0 T, ∑' n, w n * ‖ψ n t‖ ≤ (∑' n, w n * ‖ψ n 0‖) * Real.exp (K * t) := by
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  set φ : ℝ → ℝ := fun t => ∑' n, w n * ‖ψ n t‖ with hφdef
  have hφc : ContinuousOn φ (Icc 0 T) :=
    continuousOn_tsum (fun n => continuousOn_const.mul (hψ n).norm) hP
      (fun n t ht => by
        rw [Real.norm_of_nonneg (mul_nonneg (hw n) (norm_nonneg _))]
        exact hψP n t ht)
  have hGc : ContinuousOn (fun t => ∑' n, w n * ‖G n t‖) (Icc 0 T) :=
    continuousOn_tsum (fun n => continuousOn_const.mul (hG n).norm) hQ
      (fun n t ht => by
        rw [Real.norm_of_nonneg (mul_nonneg (hw n) (norm_nonneg _))]
        exact hGQ n t ht)
  have hsψ : ∀ t ∈ Icc 0 T, Summable fun n => w n * ‖ψ n t‖ := fun t ht =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (norm_nonneg _)) (fun n => hψP n t ht) hP
  have hsG : ∀ t ∈ Icc 0 T, Summable fun n => w n * ‖G n t‖ := fun t ht =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (norm_nonneg _)) (fun n => hGQ n t ht) hQ
  refine le_mul_exp_of_le_add_integral (φ := φ) (tsum_nonneg fun n =>
    mul_nonneg (hw n) (norm_nonneg _)) hK hφc
    (fun t _ => tsum_nonneg fun n => mul_nonneg (hw n) (norm_nonneg _)) (fun t ht => ?_) t₀ ht₀
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  -- interchange of the sum and the integral
  have hHasSum : HasSum (fun n => ∫ s in (0 : ℝ)..t, w n * ‖G n s‖)
      (∫ s in (0 : ℝ)..t, ∑' n, w n * ‖G n s‖) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => Q n)
      (fun n => ?_) (fun n => Eventually.of_forall fun s hs => ?_)
      (Eventually.of_forall fun s _ => hQ) intervalIntegrable_const
      (Eventually.of_forall fun s hs => ?_)
    · rw [uIoc_of_le ht.1]
      exact ((continuousOn_const.mul (hG n).norm).mono
        (Ioc_subset_Icc_self.trans hsub)).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.1] at hs
      rw [Real.norm_of_nonneg (mul_nonneg (hw n) (norm_nonneg _))]
      exact hGQ n s (hsub (Ioc_subset_Icc_self hs))
    · rw [uIoc_of_le ht.1] at hs
      exact (hsG s (hsub (Ioc_subset_Icc_self hs))).hasSum
  have hpt : ∀ n, w n * ‖ψ n t‖ ≤ w n * ‖ψ n 0‖ + ∫ s in (0 : ℝ)..t, w n * ‖G n s‖ := by
    intro n
    rw [heq n t ht, intervalIntegral.integral_const_mul, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hw n)
    exact (norm_add_le _ _).trans
      (add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1))
  calc φ t ≤ ∑' n, (w n * ‖ψ n 0‖ + ∫ s in (0 : ℝ)..t, w n * ‖G n s‖) :=
        Summable.tsum_le_tsum hpt (hsψ t ht) ((hsψ 0 h0).add hHasSum.summable)
    _ = φ 0 + ∫ s in (0 : ℝ)..t, ∑' n, w n * ‖G n s‖ := by
        rw [(hsψ 0 h0).tsum_add hHasSum.summable, hHasSum.tsum_eq]
    _ ≤ φ 0 + ∫ s in (0 : ℝ)..t, K * φ s := by
        gcongr
        exact intervalIntegral.integral_mono_on ht.1 ((hGc.mono hsub).intervalIntegrable_of_Icc
          ht.1) ((continuousOn_const.mul (hφc.mono hsub)).intervalIntegrable_of_Icc ht.1)
          fun s hs => hbound s (hsub hs)
    _ = φ 0 + K * ∫ s in (0 : ℝ)..t, φ s := by rw [intervalIntegral.integral_const_mul]

end WaveTurbulence.NLS

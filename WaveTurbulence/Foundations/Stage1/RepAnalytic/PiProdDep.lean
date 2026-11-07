/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Products of absolutely summable families over a dependent product of index types

The modes of the several time-Fourier superpositions of one term (`K*_Q`, `K*_T`, `K̃^U`) live in the
different types `Fin r_i → ℤ`; the joint index is the dependent product.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open Finset
open scoped ENNReal

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

theorem hasSum_pi_prod_dep : ∀ (n : ℕ) {M : Fin n → Type*} (a : ∀ i, M i → 𝕜),
    (∀ i, Summable fun m => ‖a i m‖) →
    Summable (fun m : ∀ i, M i => ‖∏ i, a i (m i)‖) ∧
      HasSum (fun m : ∀ i, M i => ∏ i, a i (m i)) (∏ i, ∑' m, a i m)
  | 0, M, a, _ => by
    refine ⟨?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      simpa using (hasSum_fintype (fun _ : (∀ i : Fin 0, M i) => (1 : ℝ))).summable
    · simp
  | n + 1, M, a, hs => by
    obtain ⟨hsn, hhs⟩ := hasSum_pi_prod_dep n (M := fun i => M i.succ) (fun i => a i.succ)
      (fun i => hs i.succ)
    have hmul : Summable fun p : M 0 × (∀ i : Fin n, M i.succ) =>
        ‖a 0 p.1‖ * ‖∏ i : Fin n, a i.succ (p.2 i)‖ :=
      summable_mul_of_summable_norm (f := fun m => ‖a 0 m‖) (g := fun m : (∀ i : Fin n, M i.succ) =>
        ‖∏ i : Fin n, a i.succ (m i)‖) (by simpa using hs 0) (by simpa using hsn)
    have h1 : Summable fun p : M 0 × (∀ i : Fin n, M i.succ) =>
        ‖a 0 p.1 * ∏ i : Fin n, a i.succ (p.2 i)‖ := by
      simpa only [norm_mul] using hmul
    have hcons : ∀ p : M 0 × (∀ i : Fin n, M i.succ),
        ∏ i, a i (Fin.consEquiv M p i) = a 0 p.1 * ∏ i : Fin n, a i.succ (p.2 i) := by
      intro p
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    refine ⟨?_, ?_⟩
    · rw [← (Fin.consEquiv M).summable_iff]
      refine h1.congr fun p => ?_
      simp only [Function.comp]
      rw [hcons]
    · rw [← (Fin.consEquiv M).hasSum_iff]
      have h0 : HasSum (fun m => a 0 m) (∑' m, a 0 m) := (Summable.of_norm (hs 0)).hasSum
      have h2 := h0.mul hhs (Summable.of_norm h1 |>.congr fun p => by simp)
      rw [Fin.prod_univ_succ]
      convert h2 using 1
      funext p
      simp only [Function.comp, hcons]

theorem ennreal_tsum_pi_prod_dep : ∀ (n : ℕ) {M : Fin n → Type*} (f : ∀ i, M i → ℝ≥0∞),
    ∑' m : ∀ i, M i, ∏ i, f i (m i) = ∏ i, ∑' m, f i m
  | 0, M, f => by simp
  | n + 1, M, f => by
    rw [← (Fin.consEquiv M).tsum_eq, Fin.prod_univ_succ]
    have : ∀ p : M 0 × (∀ i : Fin n, M i.succ), ∏ i, f i (Fin.consEquiv M p i) =
        f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
      intro p
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    simp_rw [this]
    rw [ENNReal.tsum_prod' (f := fun p : M 0 × (∀ i : Fin n, M i.succ) =>
      f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)),
      ← ennreal_tsum_pi_prod_dep n (M := fun i => M i.succ) (fun i => f i.succ),
      ← ENNReal.tsum_mul_right]
    exact tsum_congr fun a => (ENNReal.tsum_mul_left (a := f 0 a))

end WaveTurbulence.RepAnalytic

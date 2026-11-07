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

/-! # Products of series over a finite index set

`∏_i ∑'_m a_i(m) = ∑'_{m : ι → M} ∏_i a_i(m_i)` for absolutely summable families (and for `ℝ≥0∞`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open Finset
open scoped ENNReal

variable {M : Type*} {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
theorem prod_cons_eq {n : ℕ} (a : Fin (n + 1) → M → 𝕜) (p : M × (Fin n → M)) :
    ∏ i, a i (Fin.consEquiv (fun _ : Fin (n + 1) => M) p i) =
      a 0 p.1 * ∏ i : Fin n, a i.succ (p.2 i) := by
  simp [Fin.prod_univ_succ, Fin.consEquiv]

theorem hasSum_pi_prod_fin : ∀ (n : ℕ) (a : Fin n → M → 𝕜), (∀ i, Summable fun m => ‖a i m‖) →
    Summable (fun m : Fin n → M => ‖∏ i, a i (m i)‖) ∧
      HasSum (fun m : Fin n → M => ∏ i, a i (m i)) (∏ i, ∑' m, a i m)
  | 0, a, _ => by
    refine ⟨?_, ?_⟩
    · simpa using (hasSum_fintype (fun _ : Fin 0 → M => (1 : ℝ))).summable
    · simpa using hasSum_fintype (fun _ : Fin 0 → M => (1 : 𝕜))
  | n + 1, a, hs => by
    obtain ⟨hsn, hhs⟩ := hasSum_pi_prod_fin n (fun i => a i.succ) (fun i => hs i.succ)
    have hmul : Summable fun p : M × (Fin n → M) => ‖a 0 p.1‖ * ‖∏ i : Fin n, a i.succ (p.2 i)‖ :=
      summable_mul_of_summable_norm (f := fun m => ‖a 0 m‖) (g := fun m : Fin n → M =>
        ‖∏ i : Fin n, a i.succ (m i)‖) (by simpa using hs 0) (by simpa using hsn)
    have h1 : Summable fun p : M × (Fin n → M) => ‖a 0 p.1 * ∏ i : Fin n, a i.succ (p.2 i)‖ := by
      simpa only [norm_mul] using hmul
    refine ⟨?_, ?_⟩
    · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => M)).summable_iff]
      refine h1.congr fun p => ?_
      simp only [Function.comp]
      rw [prod_cons_eq]
    · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => M)).hasSum_iff]
      have h0 : HasSum (fun m => a 0 m) (∑' m, a 0 m) := (Summable.of_norm (hs 0)).hasSum
      have h2 := h0.mul hhs (Summable.of_norm h1 |>.congr fun p => by simp)
      rw [Fin.prod_univ_succ]
      convert h2 using 1
      funext p
      simp only [Function.comp, prod_cons_eq]


theorem hasSum_pi_prod {ι : Type*} [Fintype ι] (a : ι → M → 𝕜) (hs : ∀ i, Summable fun m => ‖a i m‖) :
    Summable (fun m : ι → M => ‖∏ i, a i (m i)‖) ∧
      HasSum (fun m : ι → M => ∏ i, a i (m i)) (∏ i, ∑' m, a i m) := by
  classical
  set e := Fintype.equivFin ι with he
  obtain ⟨h1, h2⟩ := hasSum_pi_prod_fin (Fintype.card ι) (fun j => a (e.symm j)) (fun j => hs _)
  set φ : (ι → M) ≃ (Fin (Fintype.card ι) → M) := Equiv.arrowCongr e (Equiv.refl M) with hφ
  have hp : ∀ m : ι → M, ∏ i, a i (m i) = ∏ j, a (e.symm j) (φ m j) := by
    intro m
    rw [← Equiv.prod_comp e.symm]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hφ, Equiv.arrowCongr]
  have hq : ∏ i, ∑' m, a i m = ∏ j, ∑' m, a (e.symm j) m := (Equiv.prod_comp e.symm _).symm
  refine ⟨?_, ?_⟩
  · refine (φ.summable_iff.2 h1).congr fun m => ?_
    simp only [Function.comp, hp]
  · rw [hq]
    refine (φ.hasSum_iff.2 h2).congr_fun ?_
    intro m
    simp only [Function.comp, hp]


theorem ennreal_tsum_pi_prod_fin : ∀ (n : ℕ) (f : Fin n → M → ℝ≥0∞),
    ∑' m : Fin n → M, ∏ i, f i (m i) = ∏ i, ∑' m, f i m
  | 0, f => by simp
  | n + 1, f => by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => M)).tsum_eq, Fin.prod_univ_succ]
    have : ∀ p : M × (Fin n → M), ∏ i, f i (Fin.consEquiv (fun _ : Fin (n + 1) => M) p i) =
        f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
      intro p
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    simp_rw [this]
    rw [ENNReal.tsum_prod' (f := fun p : M × (Fin n → M) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)),
      ← ennreal_tsum_pi_prod_fin n (fun i => f i.succ), ← ENNReal.tsum_mul_right]
    exact tsum_congr fun a => (ENNReal.tsum_mul_left (a := f 0 a))

theorem ennreal_tsum_pi_prod {ι : Type*} [Fintype ι] (f : ι → M → ℝ≥0∞) :
    ∑' m : ι → M, ∏ i, f i (m i) = ∏ i, ∑' m, f i m := by
  classical
  set e := Fintype.equivFin ι with he
  have h2 := ennreal_tsum_pi_prod_fin (Fintype.card ι) (fun j => f (e.symm j))
  set φ : (ι → M) ≃ (Fin (Fintype.card ι) → M) := Equiv.arrowCongr e (Equiv.refl M) with hφ
  have hp : ∀ m : ι → M, ∏ i, f i (m i) = ∏ j, f (e.symm j) (φ m j) := by
    intro m
    rw [← Equiv.prod_comp e.symm]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hφ, Equiv.arrowCongr]
  have hq : ∏ i, ∑' m, f i m = ∏ j, ∑' m, f (e.symm j) m := (Equiv.prod_comp e.symm _).symm
  rw [hq, ← h2, ← φ.tsum_eq]
  exact tsum_congr fun m => hp _

end WaveTurbulence.VineEstS3.Eng

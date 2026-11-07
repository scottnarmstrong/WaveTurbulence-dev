/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! # Finite product bookkeeping for one split maximal ladder -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen

/-- Group actual new ladder powers by their old parent. -/
theorem prod_parent_weights {I J : Type*} [DecidableEq I] (S : Finset I) (T : Finset J)
    (parent : J → I) (hp : ∀ t ∈ T, parent t ∈ S) (w : I → ℝ) (m : J → ℕ) :
    (∏ t ∈ T, w (parent t) ^ m t) =
      ∏ s ∈ S, w s ^ (∑ t ∈ T.filter (fun t => parent t = s), m t) := by
  classical
  rw [← prod_fiberwise_of_maps_to hp]
  apply prod_congr rfl
  intro s _
  calc
    _ = ∏ t ∈ T.filter (fun t => parent t = s), w s ^ m t := by
      apply prod_congr rfl
      intro t ht
      rw [(mem_filter.mp ht).2]
    _ = _ := prod_pow_eq_pow_sum _ _ _

/-- If only one old ladder loses at most two total length units, then the
whole product loses at most the square of the uniform single-rung weight. -/
theorem prod_ladder_powers_le_of_one_length_loss {I J : Type*} [DecidableEq I]
    (S : Finset I) (T : Finset J) (parent : J → I) (hp : ∀ t ∈ T, parent t ∈ S)
    (w : I → ℝ) (n : I → ℕ) (m : J → ℕ) (bad : I) {Q : ℝ} (hQ : 1 ≤ Q)
    (hw : ∀ s ∈ S, 1 ≤ w s) (hwQ : ∀ s ∈ S, w s ≤ Q)
    (hlen : ∀ s ∈ S, n s ≤ (∑ t ∈ T.filter (fun t => parent t = s), m t) + if s = bad then 2 else 0) :
    (∏ s ∈ S, w s ^ n s) ≤ Q ^ 2 * ∏ t ∈ T, w (parent t) ^ m t := by
  classical
  let F := fun s => ∑ t ∈ T.filter (fun t => parent t = s), m t
  have hbase (s : I) (hs : s ∈ S) : 0 ≤ w s := zero_le_one.trans (hw s hs)
  have hextra : (∏ s ∈ S, w s ^ (if s = bad then 2 else 0)) ≤ Q ^ 2 := by
    have he : (∏ s ∈ S, w s ^ (if s = bad then 2 else 0)) = if bad ∈ S then w bad ^ 2 else 1 := by
      have hf (s : I) : w s ^ (if s = bad then 2 else 0) = if s = bad then w s ^ 2 else 1 := by split_ifs <;> rfl
      simp_rw [hf]
      exact prod_ite_eq' S bad (fun s => w s ^ 2)
    rw [he]
    split_ifs with hb
    · exact pow_le_pow_left₀ (hbase bad hb) (hwQ bad hb) 2
    · exact one_le_pow₀ hQ
  calc
    _ ≤ ∏ s ∈ S, w s ^ (F s + if s = bad then 2 else 0) := by
      apply prod_le_prod₀
      · intro s hs
        exact pow_nonneg (hbase s hs) _
      · intro s hs
        exact pow_le_pow_right₀ (hw s hs) (hlen s hs)
    _ = (∏ s ∈ S, w s ^ F s) * ∏ s ∈ S, w s ^ (if s = bad then 2 else 0) := by
      simp_rw [pow_add]
      rw [prod_mul_distrib]
    _ ≤ (∏ s ∈ S, w s ^ F s) * Q ^ 2 :=
      mul_le_mul_of_nonneg_left hextra (prod_nonneg fun s hs => pow_nonneg (hbase s hs) _)
    _ = _ := by rw [← prod_parent_weights S T parent hp w m]; ring

end WaveTurbulence.Degen

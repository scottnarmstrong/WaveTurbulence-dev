/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.ForestTimeOrder
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure
public import WaveTurbulence.Foundations.IncohInst.Links.Locality

/-! # Strict clock order along actual source ancestors -/

public section
namespace WaveTurbulence.IncohInst
open TTree

/-- The literal parent-child inequalities imply strict order along every nonempty path. -/
theorem time_lt_of_append (t : TTree) (τ : Path → ℝ) (h : TimeOrdered t τ)
    (p q : Path) (hq : q ≠ []) (hpq : p ++ q ∈ t.branching) : τ (p ++ q) < τ p := by
  induction q using List.reverseRecOn with
  | nil => exact False.elim (hq rfl)
  | append_singleton q i ih =>
    have he : p ++ (q ++ [i]) = (p ++ q) ++ [i] := (List.append_assoc _ _ _).symm
    rw [he] at hpq ⊢
    have hp := Comb.TreePath.branching_of_append_mem t (TTree.branching_subset_nodes t hpq)
    have hc := h (p ++ q) hp i hpq
    by_cases hnil : q = []
    · simpa only [hnil, List.append_nil] using hc
    · exact hc.trans (ih hnil hp)

/-- The source branching clock strictly decreases below any strict source ancestor. -/
theorem branch_time_lt_of_under {w : ℕ} {tree : Fin w → TTree}
    (τ : GBranch tree → ℝ)
    (h : ∀ a b : GBranch tree, b.IsChildOf a → τ b < τ a)
    (a b : GBranch tree) (hu : Links.Under a.val b.val)
    (hlen : a.val.2.length < b.val.2.length) : τ b < τ a := by
  have ho : TimeOrdered (tree a.val.1) (branchClockAt τ a.val.1) := by
    intro p hp i hi
    have hc := h (⟨(a.val.1, p), hp⟩ : GBranch tree) ⟨(a.val.1, p ++ [i]), hi⟩ ⟨rfl, i, rfl⟩
    simpa only [branchClockAt, dite_eq_left hp, dite_eq_left hi] using hc
  obtain ⟨q, hq⟩ := hu.2
  have hqn : q ≠ [] := by
    intro he
    simp only [he, List.append_nil] at hq
    exact (ne_of_lt hlen) (congrArg List.length hq)
  have hb : a.val.2 ++ q ∈ (tree a.val.1).branching := by
    rw [hq, hu.1]
    exact b.2
  have ht := time_lt_of_append (tree a.val.1) (branchClockAt τ a.val.1) ho a.val.2 q hqn hb
  have heq : branchClockAt τ a.val.1 b.val.2 = τ b := by
    rw [hu.1]
    exact branchClockAt_branch τ b
  rw [hq, heq, branchClockAt_branch] at ht
  exact ht

end WaveTurbulence.IncohInst

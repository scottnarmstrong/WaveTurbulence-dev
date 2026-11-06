/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamInsertionCapSupport
import Mathlib.Tactic

/-! # Cap support survives arbitrary insertions in the other slots -/

public section
namespace WaveTurbulence.Vine.Param

/-- Every atom of a selected cap is an old template atom. -/
theorem slotCap_old (X : VineType) : ∀ i,∀ v ∈ slotCap X i,v<X.template.n := by
  cases X <;> decide

/-- The selected cap lies consistently at one end of both marked rails.
Its end can differ between slots; reverse charts cover the first-end case. -/
theorem slotCap_marked_ports (X : VineType) : ∀ i,
    (X.template.slots[i.1].1.1 ∈ slotCap X i ∧ X.template.slots[i.1].1.2 ∉ slotCap X i ∧
      X.template.slots[i.1].2.1 ∈ slotCap X i ∧ X.template.slots[i.1].2.2 ∉ slotCap X i) ∨
    (X.template.slots[i.1].1.1 ∉ slotCap X i ∧ X.template.slots[i.1].1.2 ∈ slotCap X i ∧
      X.template.slots[i.1].2.1 ∉ slotCap X i ∧ X.template.slots[i.1].2.2 ∈ slotCap X i) := by
  cases X <;> decide

/-- Arbitrarily many outside-slot insertions cannot create a crossing of an
old cap. The source insertion count and order are unrestricted. -/
theorem fold_insertRungs_cap_crossing_old
    (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) (C : Finset ℕ)
    (hC : ∀ v ∈ C,v<T.n)
    (hs : ∀ sk ∈ xs,sk.1.1.1 ∉ C ∧ sk.1.1.2 ∉ C ∧ sk.1.2.1 ∉ C ∧ sk.1.2.2 ∉ C)
    {e : ℕ×ℕ} (he : e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds)
    (hc : ¬(e.1 ∈ C ↔ e.2 ∈ C)) : e ∈ T.bonds := by
  induction xs generalizing T with
  | nil => exact he
  | cons sk xs ih =>
    have hC' : ∀ v ∈ C,v<(insertRungs T sk.1 sk.2).n := by
      intro v hv
      rw [insertRungs_atoms]
      have := hC v hv
      omega
    have hs' : ∀ t ∈ xs,t.1.1.1 ∉ C ∧ t.1.1.2 ∉ C ∧ t.1.2.1 ∉ C ∧ t.1.2.2 ∉ C := by
      intro t ht
      exact hs t (List.mem_cons_of_mem sk ht)
    have hh := ih (insertRungs T sk.1 sk.2) hC' hs' he
    exact insertRungs_cap_crossing_old T sk.1 sk.2 C hC
      (hs sk (List.mem_cons_self)) hh hc

end WaveTurbulence.Vine.Param

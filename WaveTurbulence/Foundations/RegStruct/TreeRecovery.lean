/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.LeafAddresses
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Ordered trees are recovered from their leaf addresses

This lets surgery fidelity be checked through actual pair endpoints, avoiding
an independent and potentially inconsistent shape-only description.
-/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- The leaf addresses determine an ordered ternary tree. -/
theorem tree_eq_of_leaves_eq (t u : TTree) (h : t.leaves = u.leaves) : t = u := by
  cases t with
  | leaf =>
    cases u with
    | leaf => rfl
    | node l m r =>
      have hh : ([] : Path) ∈ (TTree.node l m r).leaves := h ▸ mem_singleton_self []
      simp only [leaves, Finset.mem_union, nil_notMem_pre, or_self] at hh
  | node l m r =>
    cases u with
    | leaf =>
      have hh : ([] : Path) ∈ (TTree.node l m r).leaves := h.symm ▸ mem_singleton_self []
      simp only [leaves, Finset.mem_union, nil_notMem_pre, or_self] at hh
    | node l' m' r' =>
      have hl : l.leaves = l'.leaves := by
        ext p
        have hh := Finset.ext_iff.mp h ((0 : Fin 3) :: p)
        simpa [leaves,cons_mem_pre] using hh
      have hm : m.leaves = m'.leaves := by
        ext p
        have hh := Finset.ext_iff.mp h ((1 : Fin 3) :: p)
        simpa [leaves,cons_mem_pre] using hh
      have hr : r.leaves = r'.leaves := by
        ext p
        have hh := Finset.ext_iff.mp h ((2 : Fin 3) :: p)
        simpa [leaves,cons_mem_pre] using hh
      rw [tree_eq_of_leaves_eq l l' hl,tree_eq_of_leaves_eq m m' hm,tree_eq_of_leaves_eq r r' hr]
termination_by structural t

/-- The forest is determined by its actual global leaf-address set. -/
theorem forest_eq_of_leaf_set_eq {w : ℕ} (t u : Fin w → TTree)
    (h : forestSet t TTree.leaves = forestSet u TTree.leaves) : t = u := by
  funext j
  apply tree_eq_of_leaves_eq
  ext p
  have hh := Finset.ext_iff.mp h (j,p)
  simpa only [mem_forestSet] using hh

end WaveTurbulence.Reg

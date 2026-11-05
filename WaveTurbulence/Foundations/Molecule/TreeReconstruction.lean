/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenEncodedIso
import Mathlib.Tactic

/-! # Ternary trees are determined by their branching addresses -/

public section
namespace WaveTurbulence.Mole
open TTree

/-- Reconstruction of a ternary tree from the actual set of branching-node
addresses, as used in DH21-2 Proposition 6.4. -/
theorem tree_eq_of_branching_eq : ∀ t u : TTree, t.branching = u.branching → t = u := by
  intro t
  induction t with
  | leaf =>
      intro u h
      cases u with
      | leaf => rfl
      | node l m r =>
          have hn : ([] : Path) ∈ TTree.leaf.branching := by
            rw [h]
            exact Finset.mem_insert_self _ _
          simp only [TTree.branching,Finset.notMem_empty] at hn
  | node l m r ihl ihm ihr =>
      intro u h
      cases u with
      | leaf =>
          have hn : ([] : Path) ∈ TTree.leaf.branching := by
            rw [← h]
            exact Finset.mem_insert_self _ _
          simp only [TTree.branching,Finset.notMem_empty] at hn
      | node l' m' r' =>
          have hc (i : Fin 3) (p : Path) :
              i::p ∈ (TTree.node l m r).branching ↔ i::p ∈ (TTree.node l' m' r').branching := by rw [h]
          have hl : l.branching = l'.branching := by
            ext p
            simpa [TTree.branching,cons_mem_pre] using hc 0 p
          have hm : m.branching = m'.branching := by
            ext p
            simpa [TTree.branching,cons_mem_pre] using hc 1 p
          have hr : r.branching = r'.branching := by
            ext p
            simpa [TTree.branching,cons_mem_pre] using hc 2 p
          rw [ihl _ hl,ihm _ hm,ihr _ hr]

/-- Once roots are ordered, the encoded molecular graph determines all
actual trees, including which roots are trivial. -/
theorem GardenEncodedIso.trees_eq {w : ℕ} {G H : Garden w} (f : GardenEncodedIso G H)
    (hroot : ∀ v : GBranch G.tree, v.1.2 = [] → (f.branches v).1.1 = v.1.1) : G.tree = H.tree := by
  funext i
  apply tree_eq_of_branching_eq
  ext p
  constructor
  · intro hp
    let v : GBranch G.tree := ⟨(i,p),hp⟩
    have he := f.branch_addresses hroot v
    have hh := (f.branches v).2
    rw [he] at hh
    exact hh
  · intro hp
    let v : GBranch H.tree := ⟨(i,p),hp⟩
    let u := f.branches.symm v
    have he := f.branch_addresses hroot u
    have huv : f.branches u = v := f.branches.apply_symm_apply v
    rw [huv] at he
    have hh := u.2
    rw [← he] at hh
    exact hh

end WaveTurbulence.Mole

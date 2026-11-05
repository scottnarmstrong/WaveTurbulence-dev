/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeDefs
public import WaveTurbulence.Foundations.Molecule.PairingParity
import Mathlib.Tactic

/-! # Trees with one or three children in TARGET `cnblock`
Unary vertices are retained CN joints. Leaves are actual path addresses,
and their cardinality remains odd under both allowed branching operations.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

/-- The generalized rooted trees used after removing CN blocks. -/
inductive GeneralizedTree where
  | leaf
  | unary (child : GeneralizedTree)
  | ternary (left middle right : GeneralizedTree)
  deriving DecidableEq

namespace GeneralizedTree

/-- Actual leaf addresses; the unique unary child occupies position zero. -/
@[expose] def leafPaths : GeneralizedTree → Finset Path
  | .leaf => {[]}
  | .unary t => TTree.pre 0 t.leafPaths
  | .ternary l m r => TTree.pre 0 l.leafPaths ∪ TTree.pre 1 m.leafPaths ∪ TTree.pre 2 r.leafPaths

private theorem pre_card (i : Fin 3) (s : Finset Path) : (TTree.pre i s).card = s.card :=
  Finset.card_image_of_injective _ List.cons_injective

private theorem pre_disjoint {i j : Fin 3} (h : i ≠ j) (s t : Finset Path) :
    Disjoint (TTree.pre i s) (TTree.pre j t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨q,hq',rfl⟩ := TTree.mem_pre.mp hp
  exact h (TTree.cons_mem_pre.mp hq).1.symm

theorem card_leafPaths_unary (t : GeneralizedTree) : (unary t).leafPaths.card = t.leafPaths.card :=
  pre_card _ _

theorem card_leafPaths_ternary (l m r : GeneralizedTree) :
    (ternary l m r).leafPaths.card = l.leafPaths.card + m.leafPaths.card + r.leafPaths.card := by
  rw [leafPaths]
  have h01 := pre_disjoint (i := 0) (j := 1) (by decide) l.leafPaths m.leafPaths
  have h02 := pre_disjoint (i := 0) (j := 2) (by decide) l.leafPaths r.leafPaths
  have h12 := pre_disjoint (i := 1) (j := 2) (by decide) m.leafPaths r.leafPaths
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02,h12⟩),
    Finset.card_union_of_disjoint h01,pre_card,pre_card,pre_card]

/-- TARGET `cnblock`: every generalized tree still has an odd number of leaves. -/
theorem odd_card_leafPaths (t : GeneralizedTree) : Odd t.leafPaths.card := by
  induction t with
  | leaf => exact ⟨0,rfl⟩
  | unary t ih => rw [card_leafPaths_unary]; exact ih
  | ternary l m r hl hm hr =>
    rw [card_leafPaths_ternary]
    exact (hl.add_odd hm).add_odd hr

/-- Ordinary ternary trees embed without changing any leaf address. -/
@[expose] def ofTTree : TTree → GeneralizedTree
  | .leaf => .leaf
  | .node l m r => .ternary (ofTTree l) (ofTTree m) (ofTTree r)

theorem leafPaths_ofTTree (t : TTree) : (ofTTree t).leafPaths = t.leaves := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [ofTTree,leafPaths,TTree.leaves,hl,hm,hr]

end GeneralizedTree
end WaveTurbulence.Mole

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCriteria
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.InducedGarden

/-! # Constructing an actual embedded couple (TARGET L846)

The source pairing condition produces the garden, its induced pairing and
its opposite root signs. Reordering the two roots makes its signature (+,−).
-/

public section

namespace WaveTurbulence.Comb
open Finset TTree

variable {w : ℕ} {tree : Fin w → TTree} {G : Garden w}

/-- The actual subtree at a valid forest node, obtained from proved extraction existence. -/
@[expose] noncomputable def nodeSubtree (a : GNode tree) : TTree :=
  Classical.choose ((subtree_exists_iff (tree a.1.1) a.1.2).mpr a.2)

theorem nodeSubtree_spec (a : GNode tree) : subtree (tree a.1.1) a.1.2 = some (nodeSubtree a) :=
  Classical.choose_spec ((subtree_exists_iff (tree a.1.1) a.1.2).mpr a.2)

/-- Two incomparable rooted subtrees, with their actual source shapes. -/
@[expose] noncomputable def twoRootSubforest (a b : GNode tree) (hab : a.Incomparable b) :
    RootedSubforest tree 2 where
  root := ![a, b]
  shape i := nodeSubtree (![a, b] i)
  subtree_eq i := nodeSubtree_spec _
  incomparable := by
    intro i j hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · exact hab
    · exact ⟨hab.2, hab.1⟩
    · exact (hne rfl).elim

/-- The selected ambient leaves are exactly the source's two subtree leaf sets. -/
theorem twoRootSubforest_leafSet (a b : GNode G.tree) (hab : a.Incomparable b) :
    RootedSubforest.leafSet (twoRootSubforest a b hab) = a.leavesBelow ∪ b.leavesBelow := by
  ext ℓ
  rw [RootedSubforest.mem_leafSet_iff]
  simp only [Finset.mem_union, GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- The source complete-pairing condition supplies the induced-garden premise. -/
theorem subCouple_forest_closed {a b : GNode G.tree} (h : IsSubCouple G a b) :
    G.CompletelyPaired (RootedSubforest.leafSet (twoRootSubforest a b (subCouple_incomparable h))) := by
  rw [twoRootSubforest_leafSet]
  exact h

/-- The actual garden of the two rooted subtrees, before possibly switching their order. -/
@[expose] noncomputable def subCoupleGarden {a b : GNode G.tree} (h : IsSubCouple G a b) : Garden 2 :=
  RootedSubforest.inducedGarden (twoRootSubforest a b (subCouple_incomparable h))
    (subCouple_forest_closed h)

/-- With the positive root first, the induced garden is a source couple. -/
theorem subCoupleGarden_isCouple_of_positive_left {a b : GNode G.tree}
    (h : IsSubCouple G a b) (ha : G.sign a = 1) : IsCouple (subCoupleGarden h) := by
  constructor
  · exact RootedSubforest.inducedGarden_plain _ _
  · funext i
    have hb : G.sign b = -1 := by rw [subCouple_sign h, ha]
    fin_cases i
    · exact ha
    · exact hb

/-- Every sub-couple condition yields a genuine couple after orienting its two roots. -/
theorem exists_embedded_couple {a b : GNode G.tree} (h : IsSubCouple G a b) :
    ∃ E : RootedSubforest G.tree 2,
      ∃ hc : G.CompletelyPaired (RootedSubforest.leafSet E),
        IsCouple (RootedSubforest.inducedGarden E hc) ∧
        RootedSubforest.leafSet E = a.leavesBelow ∪ b.leavesBelow ∧
        ((E.root 0 = a ∧ E.root 1 = b) ∨ (E.root 0 = b ∧ E.root 1 = a)) := by
  rcases Int.units_eq_one_or (G.sign a) with ha | ha
  · exact ⟨twoRootSubforest a b (subCouple_incomparable h), subCouple_forest_closed h,
      subCoupleGarden_isCouple_of_positive_left h ha, twoRootSubforest_leafSet _ _ _, Or.inl ⟨rfl, rfl⟩⟩
  · have h' : IsSubCouple G b a := by simpa only [IsSubCouple, Finset.union_comm] using h
    have hb : G.sign b = 1 := by rw [subCouple_sign h, ha, neg_neg]
    refine ⟨twoRootSubforest b a (subCouple_incomparable h'), subCouple_forest_closed h',
      subCoupleGarden_isCouple_of_positive_left h' hb, ?_, Or.inr ⟨rfl, rfl⟩⟩
    rw [twoRootSubforest_leafSet, Finset.union_comm]

/-- Embedded couple order is the sum of the orders of its two actual subtrees. -/
theorem subCoupleGarden_order {a b : GNode G.tree} (h : IsSubCouple G a b) :
    (subCoupleGarden h).order = (nodeSubtree a).order + (nodeSubtree b).order := by
  change (∑ i : Fin 2, (nodeSubtree (![a, b] i)).order) = _
  rw [Fin.sum_univ_two]
  rfl

end WaveTurbulence.Comb

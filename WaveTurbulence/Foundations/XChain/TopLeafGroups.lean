/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraft
public import WaveTurbulence.Foundations.Cumulant.ProductsFormula
/-! The disjoint nonempty groups of top-tree leaves used in propertycm. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem tree_leaves_nonempty (T : TTree) : T.leaves.Nonempty := by
  induction T with
  | leaf => simp [TTree.leaves]
  | node l m r hl _ _ =>
    obtain ⟨a, ha⟩ := hl
    exact ⟨0 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha]⟩

def topLeafGroups {w : ℕ} (top : Fin w → TTree) (j : Fin w) : Finset (GLeaf top) :=
  univ.filter (fun a => a.1.1 = j)

theorem topLeafGroups_nonempty {w : ℕ} (top : Fin w → TTree) (j : Fin w) :
    (topLeafGroups top j).Nonempty := by
  obtain ⟨a, ha⟩ := tree_leaves_nonempty (top j)
  exact ⟨⟨(j, a), ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem topLeafGroups_disjoint {w : ℕ} (top : Fin w → TTree) :
    ((univ : Finset (Fin w)) : Set (Fin w)).PairwiseDisjoint (topLeafGroups top) := by
  intro j _ k _ hjk
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hj : a.1.1 = j := (Finset.mem_filter.mp ha).2
  have hk : a.1.1 = k := (Finset.mem_filter.mp hb).2
  exact hjk (hj.symm.trans hk)

theorem biUnion_topLeafGroups {w : ℕ} (top : Fin w → TTree) :
    (univ : Finset (Fin w)).biUnion (topLeafGroups top) = univ := by
  ext a
  simp [topLeafGroups]

noncomputable def topPartitionEquiv {w : ℕ} (top : Fin w → TTree) :
    Finpartition ((univ : Finset (Fin w)).biUnion (topLeafGroups top)) ≃
      Finpartition (univ : Finset (GLeaf top)) :=
  Equiv.cast (congrArg Finpartition (biUnion_topLeafGroups top))

theorem finpartition_cast_parts {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : s = t) (P : Finpartition s) :
    ((Equiv.cast (congrArg Finpartition h)) P).parts = P.parts := by
  cases h
  rfl

theorem topPartitionEquiv_parts {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition ((univ : Finset (Fin w)).biUnion (topLeafGroups top))) :
    (topPartitionEquiv top P).parts = P.parts := finpartition_cast_parts (biUnion_topLeafGroups top) P

end WaveTurbulence.Induct

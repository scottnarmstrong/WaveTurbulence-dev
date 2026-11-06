/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LeafIncomparability

/-! # Exact original matching recovery from a guarded raw A insertion -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

def miniAPairs {w : ℕ} (x y : Address w) (k : MiniCplCode) : Finset (Pair w) :=
  {(addrExt x [0],addrExt y [k.partner 0]),(addrExt y [1],addrExt x [1]),
   (addrExt x [2],addrExt y [k.partner 2])}

theorem leaf_child_not_node {w : ℕ} (tree : Fin w → TTree) (ℓ : GLeaf tree) (i : Fin 3) :
    (addrExt ℓ.1 [i]).2 ∉ (tree (addrExt ℓ.1 [i]).1).nodes := by
  intro hn
  have he := leaf_prefix_node_eq ℓ.2 hn (List.prefix_append _ _)
  have hl := congrArg List.length he
  change ℓ.1.2.length = (ℓ.1.2 ++ [i]).length at hl
  simp only [List.length_append,List.length_singleton] at hl
  omega

theorem Raw.old_pair_not_mem_miniA {w : ℕ} (R : Raw w) (hR : R.Valid) (x y : Address w)
    (k : MiniCplCode) (hp : (x,y) ∈ R.pairs) (p : Pair w) (hmem : p ∈ R.pairs) :
    p ∉ miniAPairs x y k := by
  have hv := hR.1 _ hp
  let ℓ : GLeaf R.tree := ⟨x,hv.1⟩
  let q : GLeaf R.tree := ⟨y,hv.2.1⟩
  have hs := (hR.1 p hmem).1
  intro hn
  simp only [miniAPairs,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact leaf_child_not_node R.tree ℓ 0 (TTree.leaves_subset_nodes _ hs)
  · exact leaf_child_not_node R.tree q 1 (TTree.leaves_subset_nodes _ hs)
  · exact leaf_child_not_node R.tree ℓ 2 (TTree.leaves_subset_nodes _ hs)

theorem Raw.opA_pairs_erase_mini {w : ℕ} (R : Raw w) (hR : R.Valid) (x y : Address w)
    (k : MiniCplCode) (hp : (x,y) ∈ R.pairs) :
    (R.opA x y k).pairs \ miniAPairs x y k = R.pairs.erase (x,y) := by
  classical
  ext p
  constructor
  · intro hm
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hm
    change p ∈ R.pairs.erase (x,y) ∪ miniAPairs x y k at hm
    exact (Finset.mem_union.mp hm).resolve_right hn
  · intro hm
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hm,
      R.old_pair_not_mem_miniA hR x y k hp p (Finset.mem_of_mem_erase hm)⟩

theorem Raw.opA_pairs_injective {w : ℕ} (R T : Raw w) (hR : R.Valid) (hT : T.Valid)
    (x y : Address w) (k : MiniCplCode) (hpR : (x,y) ∈ R.pairs) (hpT : (x,y) ∈ T.pairs)
    (he : R.opA x y k = T.opA x y k) : R.pairs = T.pairs := by
  have hn := congrArg (fun U : Raw w => U.pairs \ miniAPairs x y k) he
  have hi : R.pairs.erase (x,y) = T.pairs.erase (x,y) :=
    (R.opA_pairs_erase_mini hR x y k hpR).symm.trans (hn.trans (T.opA_pairs_erase_mini hT x y k hpT))
  exact (Finset.insert_erase hpR).symm.trans ((congrArg (insert (x,y)) hi).trans (Finset.insert_erase hpT))

end WaveTurbulence.Reg.Skeleton

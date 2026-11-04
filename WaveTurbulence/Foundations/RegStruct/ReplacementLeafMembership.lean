/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationBLists
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ReplacementLeaves

/-! # Literal leaf membership under replacement of an actual rooted subtree -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Leaves outside the removed subtree retain their addresses. -/
theorem update_leaf_outside {w : ℕ} (tree : Fin w → TTree) (a z : Fin w × Path)
    (u s : TTree) (ha : Comb.subtree (tree a.1) a.2 = some u)
    (hz : z.2 ∈ (tree z.1).leaves) (hout : ¬ Below a z) :
    z.2 ∈ (updateAddressForest tree a s z.1).leaves := by
  by_cases he : z.1 = a.1
  · rw [updateAddressForest,he,Function.update_self,Comb.leaves_replaceAt_eq ha s]
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨he ▸ hz,fun hp => hout ⟨he,hp⟩⟩
  · rw [updateAddressForest,Function.update_of_ne he]
    exact hz

/-- Every leaf of the inserted subtree is present with its literal prefix. -/
theorem update_leaf_inserted {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path)
    (u s : TTree) (ha : Comb.subtree (tree a.1) a.2 = some u)
    (p : Path) (hp : p ∈ s.leaves) :
    (addrExt a p).2 ∈ (updateAddressForest tree a s (addrExt a p).1).leaves := by
  change a.2 ++ p ∈ (Function.update tree a.1 (Comb.replaceAt (tree a.1) a.2 s) a.1).leaves
  rw [Function.update_self,Comb.leaves_replaceAt_eq ha s]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)

/-- Global leaf membership of every local inserted leaf. -/
theorem update_leafAddresses_subset {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path)
    (u s : TTree) (ha : Comb.subtree (tree a.1) a.2 = some u) :
    leafAddresses s a ⊆ forestSet (updateAddressForest tree a s) TTree.leaves := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  exact (mem_forestSet _).mpr (update_leaf_inserted tree a u s ha p hp)

/-- Each endpoint of a new mini-chain pair is a leaf of its filled context. -/
theorem miniChain_endpoints_subset_context (m : MiniTreeCode) (ζ : ℤˣ) (s : TTree)
    (a : Fin 2 × Path) :
    pairEndpoints ((miniChain m).pairsAt ζ a) ⊆ leafAddresses (miniTreeContext m s) a := by
  have he := chain_leafAddresses (miniChain m) ζ s a
  rw [miniChain_plug] at he
  rw [he]
  exact Finset.subset_union_left

/-- Moving an old subtree leaf through a mini-context retains literal leaf membership. -/
theorem miniContext_old_leaf (m : MiniTreeCode) (ζ : ℤˣ) (s : TTree)
    (r : Path) (hr : r ∈ s.leaves) : [m.c,m.lone] ++ r ∈ (miniTreeContext m s).leaves := by
  have he := chain_leafAddresses (miniChain m) ζ s ((0 : Fin 1),[])
  rw [miniChain_plug,miniChain_lonePath] at he
  have hh : addrExt ((0 : Fin 1),[m.c,m.lone]) r ∈
      leafAddresses (miniTreeContext m s) (0,[]) := by
    rw [he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  obtain ⟨p,hp,hpEq⟩ := Finset.mem_image.mp hh
  have hep := congrArg Prod.snd hpEq
  simp only [addrExt,List.nil_append] at hep
  simpa only [hep] using hp

/-- Source B sends each old leaf to a leaf via the literal source relocation map. -/
theorem raw_opB_old_leaf (R : RawCpl) (a z : Fin 2 × Path) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) (hz : z.2 ∈ (R.tree z.1).leaves) :
    (RawCpl.relocate a m.c m.lone z).2 ∈
      ((R.opB a m).tree (RawCpl.relocate a m.c m.lone z).1).leaves := by
  let A : GNode R.tree := ⟨a,ha⟩
  have hspec := Comb.nodeSubtree_spec A
  have hs : (R.tree a.1).subtreeAt a.2 = Comb.nodeSubtree A := subtreeAt_eq_of_subtree _ _ _ hspec
  rw [raw_opB_update,hs]
  by_cases hb : Below a z
  · obtain ⟨r,hr⟩ := hb.2
    have hez : z = addrExt a r := Prod.ext hb.1 hr.symm
    subst z
    have hu : r ∈ (Comb.nodeSubtree A).leaves := (Comb.subtree_leaves_iff hspec r).mpr hz
    have he : RawCpl.relocate a m.c m.lone (addrExt a r) = addrExt a ([m.c,m.lone] ++ r) := by
      have hl := relocate_respects_desc a a m.c m.lone ⟨rfl,List.prefix_refl _⟩
      rw [hl _,relocate_self,addrExt_append]
    rw [he]
    exact update_leaf_inserted R.tree a _ _ hspec _ (miniContext_old_leaf m 1 _ r hu)
  · rw [relocate_eq_of_not_below a m.c m.lone z hb]
    exact update_leaf_outside R.tree a z _ _ hspec hz hb

/-- Both newly inserted mini-chain endpoints are actual leaves after source B. -/
theorem raw_opB_new_endpoints (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    pairEndpoints ((miniChain m).pairsAt (nodeSign ![1,-1] a) a) ⊆
      forestSet (R.opB a m).tree TTree.leaves := by
  let A : GNode R.tree := ⟨a,ha⟩
  have hspec := Comb.nodeSubtree_spec A
  have hs : (R.tree a.1).subtreeAt a.2 = Comb.nodeSubtree A := subtreeAt_eq_of_subtree _ _ _ hspec
  rw [raw_opB_update,hs]
  exact (miniChain_endpoints_subset_context m _ _ a).trans
    (update_leafAddresses_subset R.tree a _ _ hspec)

end WaveTurbulence.Reg

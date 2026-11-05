/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainLoneExclusion
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds
public import WaveTurbulence.Foundations.RegStruct.PairNaturality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniLeafRegion

/-! # Internal chain endpoints lie strictly outside the lone subtree in every frame -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

 theorem chain_endpoint_frame {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Address w)
    (z : Address w) (hz : z ∈ pairEndpoints (X.pairsAt ζ a)) :
    ∃ p : Path, z = addrExt a p ∧ p ∈ (X.plug ζ .leaf).leaves ∧ p ≠ X.lonePath := by
  let f : Address 1 → Address w := fun x => addrExt a x.2
  have hf : ∀ x p, f (addrExt x p) = addrExt (f x) p := by
    intro x p
    simp only [f,addrExt,List.append_assoc]
  have hm := chain_pairsAt_map X f hf ζ ((0 : Fin 1),[])
  have hroot : f (0,[]) = a := by simp [f,addrExt]
  rw [hroot] at hm
  obtain ⟨q,hq,hzq⟩ := (mem_pairEndpoints_iff _ _).mp hz
  rw [hm] at hq
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq
  subst q
  rcases hzq with hzq | hzq
  · refine ⟨r.1.2,hzq,(decodedTree_pairs_valid X ζ r hr).1,?_⟩
    intro he
    apply chainLone_not_pairEndpoints X ζ
    exact (mem_pairEndpoints_iff _ _).mpr ⟨r,hr,Or.inl (Prod.ext (Subsingleton.elim _ _) he.symm)⟩
  · refine ⟨r.2.2,hzq,(decodedTree_pairs_valid X ζ r hr).2,?_⟩
    intro he
    apply chainLone_not_pairEndpoints X ζ
    exact (mem_pairEndpoints_iff _ _).mpr ⟨r,hr,Or.inr (Prod.ext (Subsingleton.elim _ _) he.symm)⟩

 theorem chain_endpoint_not_below_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a z : Address w)
    (hz : z ∈ pairEndpoints (X.pairsAt ζ a)) : ¬ Below (addrExt a X.lonePath) z := by
  obtain ⟨p,rfl,hp,hne⟩ := chain_endpoint_frame X ζ a z hz
  intro hl
  have hprefix := (below_frames_iff a X.lonePath p).mp hl
  exact hne ((leaf_prefix_node_eq (chain_lone_mem_leaves X ζ)
    ((Comb.TreePath.mem_nodes_iff _ _).mpr (Or.inl hp)) hprefix).symm)

end WaveTurbulence.Reg.Skeleton

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds


/-! # Chain pair endpoints lie before or off its terminal hole -/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}
open Finset

/-- Every leaf address is an actual node address of the same rooted tree. -/
theorem leafAddresses_subset_nodeAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) :
    leafAddresses t a ⊆ nodeAddresses t a :=
  Finset.image_subset_image (TTree.leaves_subset_nodes t)

/-- Every listed couple endpoint is one of its represented nodes. -/
theorem couple_pairEndpoints_subset_nodes {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    pairEndpoints (Q.pairsAt a b) ⊆ coupleNodes Q a b := by
  rw [← couple_leafAddresses,← couple_nodeAddresses]
  exact Finset.union_subset_union (leafAddresses_subset_nodeAddresses _ _)
    (leafAddresses_subset_nodeAddresses _ _)

private theorem subset_with_extra_left {α : Type*} [DecidableEq α]
    (A B C D E : Finset α) : B ∪ C ∪ D ∪ E ⊆ A ∪ B ∪ C ∪ D ∪ E := by
  simpa only [Finset.union_assoc] using
    (Finset.subset_union_right (s₁ := A) (s₂ := B ∪ C ∪ D ∪ E))

/-- Every listed chain endpoint is a represented node, not part of its unfilled hole. -/
theorem chain_pairEndpoints_subset_nodes {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    pairEndpoints (X.pairsAt ζ a) ⊆ chainNodes X ζ a := by
  cases X with
  | nil => simp [RegChain.pairsAt,pairEndpoints,chainNodes]
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1
    all_goals
      simp only [RegChain.pairsAt,chainNodes,hr,hg,ite_true,ite_false,pairEndpoints_append]
      apply Finset.Subset.trans
        (Finset.union_subset_union
          (Finset.union_subset_union
            (Finset.union_subset_union (couple_pairEndpoints_subset_nodes r _ _)
              (couple_pairEndpoints_subset_nodes g _ _))
            (chain_pairEndpoints_subset_nodes i _ _))
          (chain_pairEndpoints_subset_nodes s _ _))
      exact subset_with_extra_left _ _ _ _ _
termination_by structural X

/-- Both endpoints of each actual chain pair lie outside the terminal rooted subtree. -/
theorem chain_pair_not_below_lone (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (p : (Fin w × Path) × (Fin w × Path)) (hp : p ∈ X.pairsAt ζ a) :
    ¬ Below (addrExt a X.lonePath) p.1 ∧ ¬ Below (addrExt a X.lonePath) p.2 := by
  constructor
  · apply chainNodes_not_below_lone X ζ a p.1
    apply chain_pairEndpoints_subset_nodes X ζ a
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩
  · apply chainNodes_not_below_lone X ζ a p.2
    apply chain_pairEndpoints_subset_nodes X ζ a
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩

/-- Inserting at or below the terminal hole leaves every existing chain pair untouched. -/
theorem relocate_pairs_below_chain_hole (X : RegChain) (ζ : ℤˣ)
    (a target : Fin w × Path) (c l : Fin 3) (ht : Below (addrExt a X.lonePath) target) :
    (X.pairsAt ζ a).map (fun p =>
      (WaveTurbulence.Reg.Skeleton.relocate target c l p.1,WaveTurbulence.Reg.Skeleton.relocate target c l p.2)) = X.pairsAt ζ a := by
  have hmap : (X.pairsAt ζ a).map (fun p =>
      (WaveTurbulence.Reg.Skeleton.relocate target c l p.1,WaveTurbulence.Reg.Skeleton.relocate target c l p.2)) =
      (X.pairsAt ζ a).map id := by
    apply List.map_congr_left
    intro p hp
    have hloc := chain_pair_not_below_lone X ζ a p hp
    apply Prod.ext
    · exact relocate_eq_of_not_below _ _ _ _ (fun h => hloc.1 (below_trans ht h))
    · exact relocate_eq_of_not_below _ _ _ _ (fun h => hloc.2 (below_trans ht h))
  simpa only [List.map_id] using hmap

end WaveTurbulence.Reg.Skeleton.BContext

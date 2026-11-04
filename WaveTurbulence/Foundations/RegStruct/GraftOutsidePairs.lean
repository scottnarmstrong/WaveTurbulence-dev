/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PrefixRelocationNaturality

/-! # The old pair list outside a graft is disjoint from both inserted root frames -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Every endpoint in the erased outside block is an old leaf in neither graft root. -/
theorem erasedPair_endpoint_incomp (Q : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (z : Fin 2 × Path) (hz : z ∈ pairEndpoints (Q.raw.2.erase (x,y))) :
    IncompAddr x z ∧ IncompAddr y z := by
  have hmem : z ∈ pairEndpoints Q.raw.2 \ {x,y} := by rw [← pairEndpoints_erase Q x y hxy]; exact hz
  have hold := (Finset.mem_sdiff.mp hmem).1
  have hout := (Finset.mem_sdiff.mp hmem).2
  have hzLeaf : z.2 ∈ (coupleForest Q z.1).leaves := by
    apply (mem_forestSet _).mp
    rw [coupleForest_leaf_set]
    exact hold
  have hxLeaf := (decodedCouple_pairs_valid Q (x,y) hxy).1
  have hyLeaf := (decodedCouple_pairs_valid Q (x,y) hxy).2
  have hxz : x ≠ z := fun he => hout (Finset.mem_insert.mpr (Or.inl he.symm))
  have hyz : y ≠ z := fun he => hout (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he.symm)))
  exact ⟨leaf_addresses_incomp (coupleForest Q) x z hxLeaf hzLeaf hxz,
    leaf_addresses_incomp (coupleForest Q) y z hyLeaf hzLeaf hyz⟩

/-- Every framed address lies below one of the two selected roots. -/
theorem frameAddress_below (x y z : Fin 2 × Path) :
    Below x (frameAddress x y z) ∨ Below y (frameAddress x y z) := by
  obtain ⟨j,p⟩ := z
  fin_cases j
  · left
    simpa [frameAddress] using below_extend x p
  · right
    simpa [frameAddress] using below_extend y p

/-- No inserted address can equal an endpoint of the outside old pair block. -/
theorem frameAddress_ne_outside (Q : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (z u : Fin 2 × Path) (hu : u ∈ pairEndpoints (Q.raw.2.erase (x,y))) : frameAddress x y z ≠ u := by
  intro he
  have hi := erasedPair_endpoint_incomp Q x y hxy u hu
  rcases frameAddress_below x y z with h | h
  · exact hi.1.1 (he ▸ h)
  · exact hi.2.1 (he ▸ h)

/-- Hence no mapped local pair occurs in the old erased block. -/
theorem framed_pair_not_mem_outside (Q : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) :
    (frameAddress x y p.1,frameAddress x y p.2) ∉ Q.raw.2.erase (x,y) := by
  intro hp
  apply frameAddress_ne_outside Q x y hxy p.1 (frameAddress x y p.1) _ rfl
  exact (mem_pairEndpoints_iff _ _).mpr ⟨_,hp,Or.inl rfl⟩

/-- Source relocation at any inserted node leaves all outside pairs unchanged. -/
theorem relocate_outside_pairs_fixed (Q : RegCpl) (x y a : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (c l : Fin 3) :
    (Q.raw.2.erase (x,y)).map (fun p =>
      (RawCpl.relocate (frameAddress x y a) c l p.1,RawCpl.relocate (frameAddress x y a) c l p.2)) =
      Q.raw.2.erase (x,y) := by
  have hfix : ∀ z ∈ pairEndpoints (Q.raw.2.erase (x,y)),
      RawCpl.relocate (frameAddress x y a) c l z = z := by
    intro z hz
    have hi := erasedPair_endpoint_incomp Q x y hxy z hz
    rcases frameAddress_below x y a with ha | ha
    · exact relocate_eq_of_not_below _ _ _ _ ((hi.1.descendants ha ⟨rfl,List.prefix_refl _⟩).1)
    · exact relocate_eq_of_not_below _ _ _ _ ((hi.2.descendants ha ⟨rfl,List.prefix_refl _⟩).1)
  have he : (Q.raw.2.erase (x,y)).map (fun p =>
      (RawCpl.relocate (frameAddress x y a) c l p.1,RawCpl.relocate (frameAddress x y a) c l p.2)) =
      (Q.raw.2.erase (x,y)).map id := by
    apply List.map_congr_left
    intro p hp
    exact Prod.ext (hfix p.1 ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩))
      (hfix p.2 ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩))
  simpa only [List.map_id] using he

end WaveTurbulence.Reg

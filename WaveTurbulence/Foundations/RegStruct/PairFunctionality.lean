/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSlots

/-! # Unique partners and no duplicate pairs from endpoint bijectivity -/

public section
namespace WaveTurbulence.Reg
open TTree

variable {w : ℕ} (tree : Fin w → TTree)
  (P : List ((Fin w × Path) × (Fin w × Path)))
  (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)

/-- Every unordered listed pair is represented by one slot and its opposite endpoint. -/
theorem pair_slot_witness (x y : Fin w × Path) (h : (x,y) ∈ symmPairs P) :
    ∃ s : Fin P.length × Fin 2,
      (endpointLeaf tree P hv s).1 = x ∧
      (endpointLeaf tree P hv ((pairSlots P.length).pair s)).1 = y := by
  rcases (mem_symmPairs_iff P (x,y)).mp h with h | h
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp h
    refine ⟨(⟨i,hi⟩,0),?_⟩
    change P[i].1 = x ∧ P[i].2 = y
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp h
    refine ⟨(⟨i,hi⟩,1),?_⟩
    change P[i].2 = x ∧ P[i].1 = y
    exact ⟨congrArg Prod.snd he,congrArg Prod.fst he⟩

variable (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
  (hn : P.length * 2 = Fintype.card (GLeaf tree))

include tree hv hc hn

/-- A complete pair list with the exact endpoint count assigns a unique partner. -/
theorem pair_relation_functional {x y z : Fin w × Path}
    (hy : (x,y) ∈ symmPairs P) (hz : (x,z) ∈ symmPairs P) : y = z := by
  obtain ⟨s,hs,hs'⟩ := pair_slot_witness tree P hv x y hy
  obtain ⟨t,ht,ht'⟩ := pair_slot_witness tree P hv x z hz
  have he : endpointEquiv tree P hv hc hn s = endpointEquiv tree P hv hc hn t :=
    Subtype.ext (hs.trans ht.symm)
  have hst := (endpointEquiv tree P hv hc hn).injective he
  subst t
  exact hs'.symm.trans ht'

/-- No endpoint is its own partner. -/
theorem pair_relation_no_fixed (x : Fin w × Path) : (x,x) ∉ symmPairs P := by
  intro h
  obtain ⟨s,hs,hs'⟩ := pair_slot_witness tree P hv x x h
  have he : endpointEquiv tree P hv hc hn s =
      endpointEquiv tree P hv hc hn ((pairSlots P.length).pair s) :=
    Subtype.ext (hs.trans hs'.symm)
  have hfix := ((endpointEquiv tree P hv hc hn).injective he).symm
  have hm := ((pairSlots P.length).pair_eq_iff s).mp hfix
  exact hm rfl

/-- A complete exact-size pair list has no duplicate entries. -/
theorem pair_list_nodup : P.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have he : endpointEquiv tree P hv hc hn (i,0) = endpointEquiv tree P hv hc hn (j,0) := by
    apply Subtype.ext
    exact congrArg Prod.fst hij
  exact congrArg Prod.fst ((endpointEquiv tree P hv hc hn).injective he)

end WaveTurbulence.Reg

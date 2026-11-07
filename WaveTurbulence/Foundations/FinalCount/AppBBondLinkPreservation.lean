/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondPairPreservation
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # Selected links away from a removed bond's endpoints survive exactly -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_link_eraseBond_of_disjoint (M : Molecule V D) (e : D) {S : Finset V}
    (hS : AppbLink M S) (hdisj : Disjoint S {M.atom e,M.atom (M.mate e)}) :
    AppbLink (eraseBond M e) S := by
  have hne {a b : V} (ha : a ∈ S) (hb : b ∈ S) : M.ends e ≠ s(a,b) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact disjoint_left.mp hdisj (h.1.symm ▸ ha) (by simp)
    · exact disjoint_left.mp hdisj (h.1.symm ▸ hb) (by simp)
  obtain ⟨u,v,hL,rfl⟩ := hS
  have hm (j : Fin 2) : u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := by
    constructor <;> simp [Molecule.ladderAtoms]
  refine ⟨u,v,⟨hL.1,hL.2.1,hL.2.2.1,?_,?_⟩,rfl⟩
  · intro j
    rw [appb_eraseBond_bondsBetween_eq M e _ _ (hne (hm j).1 (hm j).2)]
    exact hL.2.2.2.1 j
  · intro j
    obtain ⟨hu,hv,hd⟩ := hL.2.2.2.2 j
    rw [appb_eraseBond_bondsBetween_eq M e _ _ (hne (hm j.castSucc).1 (hm j.succ).1),
      appb_eraseBond_bondsBetween_eq M e _ _ (hne (hm j.castSucc).2 (hm j.succ).2),
      appb_eraseBond_directed_iff M e _ _ (hne (hm j.castSucc).1 (hm j.succ).1),
      appb_eraseBond_directed_iff M e _ _ (hne (hm j.succ).2 (hm j.castSucc).2)]
    exact ⟨hu,hv,hd⟩

/-- Removing both endpoints loses only a subset of the links that can be
retained after deleting their bond. -/
theorem appb_endpoint_deleted_links_subset (M : Molecule V D) (e : D) :
    appbLinks (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}) ⊆ appbLinks (eraseBond M e) := by
  intro S hS
  apply (mem_appbLinks _ S).mpr
  have h := (appb_link_eraseAtoms_iff M {M.atom e,M.atom (M.mate e)} S).mp ((mem_appbLinks _ S).mp hS)
  exact appb_link_eraseBond_of_disjoint M e h.1 h.2

end WaveTurbulence.Mole

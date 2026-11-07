/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBLinks
import Mathlib.Tactic

/-! # Exact bond multiplicities and selected links after reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_addBond_bondsBetween (M : Molecule V D) (a b u v : V) :
    (addBond M a b).bondsBetween u v = M.bondsBetween u v + (if s(a,b) = s(u,v) then 1 else 0) := by
  classical
  let p : D ⊕ Bool → Prop := fun x => (addBond M a b).out x = true ∧ (addBond M a b).ends x = s(u,v)
  have he : univ.filter p = (univ.filter (fun x : D => p (.inl x))).disjSum
      (univ.filter (fun x : Bool => p (.inr x))) := by
    ext x
    cases x <;> simp
  have hl : (addBond M a b).bondsBetween u v = (univ.filter p).card := by
    simp only [Molecule.bondsBetween,Molecule.bonds,filter_filter,p]
  rw [hl,he,card_disjSum]
  change (univ.filter (fun x : D => M.out x = true ∧ M.ends x = s(u,v))).card+
    (univ.filter (fun t : Bool => t = true ∧
      s((if t then a else b),(if !t then a else b)) = s(u,v))).card = _
  have hb : (univ.filter (fun t : Bool => t = true ∧
      s((if t then a else b),(if !t then a else b)) = s(u,v))) =
      (if s(a,b) = s(u,v) then {true} else ∅) := by
    ext t
    by_cases h : s(a,b) = s(u,v)
    · rw [if_pos h]
      cases t <;> simp_all
    · rw [if_neg h]
      cases t <;> simp_all
  rw [hb]
  split_ifs <;> simp_all [Molecule.bondsBetween,Molecule.bonds,filter_filter]

theorem appb_addBond_directed_iff (M : Molecule V D) (a b u v : V)
    (hne : s(a,b) ≠ s(u,v)) : (addBond M a b).Directed u v ↔ M.Directed u v := by
  constructor
  · rintro ⟨x,ho,hu,hv⟩
    rcases x with x | t
    · exact ⟨x,ho,hu,hv⟩
    · cases t
      · contradiction
      · change a = u at hu
        change b = v at hv
        exact False.elim (hne (by rw [hu,hv]))
  · rintro ⟨x,ho,hu,hv⟩
    exact ⟨Sum.inl x,ho,hu,hv⟩

theorem appb_link_addBond_of_disjoint (M : Molecule V D) (a b : V) {S : Finset V}
    (hS : AppbLink M S) (hdisj : Disjoint S {a,b}) : AppbLink (addBond M a b) S := by
  classical
  have hne {u v : V} (hu : u ∈ S) (hv : v ∈ S) : s(a,b) ≠ s(u,v) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact disjoint_left.mp hdisj (h.1.symm ▸ hu) (by simp)
    · exact disjoint_left.mp hdisj (h.1.symm ▸ hv) (by simp)
  obtain ⟨u,v,hL,rfl⟩ := hS
  have hm (j : Fin 2) : u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := by
    constructor <;> simp [Molecule.ladderAtoms]
  refine ⟨u,v,⟨hL.1,hL.2.1,?_,?_,?_⟩,rfl⟩
  · intro j
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hL.2.2.1 j).1),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hL.2.2.1 j).2)⟩
  · intro j
    rw [appb_addBond_bondsBetween,if_neg (hne (hm j).1 (hm j).2),add_zero]
    exact hL.2.2.2.1 j
  · intro j
    obtain ⟨hu,hv,hd⟩ := hL.2.2.2.2 j
    rw [appb_addBond_bondsBetween,if_neg (hne (hm j.castSucc).1 (hm j.succ).1),add_zero,
      appb_addBond_bondsBetween,if_neg (hne (hm j.castSucc).2 (hm j.succ).2),add_zero,
      appb_addBond_directed_iff M a b _ _ (hne (hm j.castSucc).1 (hm j.succ).1),
      appb_addBond_directed_iff M a b _ _ (hne (hm j.succ).2 (hm j.castSucc).2)]
    exact ⟨hu,hv,hd⟩

end WaveTurbulence.Mole

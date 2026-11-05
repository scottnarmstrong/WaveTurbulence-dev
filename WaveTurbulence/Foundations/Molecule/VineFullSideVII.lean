/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVII
public import WaveTurbulence.Foundations.Molecule.VineSideVIIData
public import WaveTurbulence.Foundations.Molecule.VineSideLadderClosure
public import WaveTurbulence.Foundations.Molecule.VineSlotExternalNeighbors
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
import Mathlib.Tactic

/-! # Exact ordinary block geometry in the type-VII side ladder -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every connected block larger than a double bond avoiding the outer
joints in type VII is the entire side core and cyan ladder, with joints
exactly at core atoms7 and8. No side containment or incidence premise is added. -/
theorem typeVII_inner_full_side (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) :
    ∃ kr kc kg,R.k=[kr,kc,kg] ∧
      (∀ v ∈ S,v ∈ A ↔ R.f v=4 ∨ R.f v=5 ∨ R.f v=6 ∨ R.f v=7 ∨ R.f v=8 ∨
        (11+2*kr ≤ R.f v ∧ R.f v<11+2*kr+2*kc)) ∧
      ({x,y} : Finset V)={(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} := by
  obtain ⟨kr,kc,kg,hks,hside⟩ := typeVII_inner_side_region M hM R hS hA hC hAS hcard ha hb
  let c : Fin 11 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 11) : R.f (c i)=i.1 := R.label_coreAtom i
  have core_eq {z : V} (hz : z ∈ S) (i : Fin 11) (he : R.f z=i.1) : z=c i :=
    R.injOn hz (R.coreAtom i).2 (he.trans (hlabelc i).symm)
  obtain ⟨D,hmem,hlabels⟩ := typeVII_side_data M R kr kc kg hks
  have hleft := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,0,2,3⟩ (by exact List.mem_cons_self)
  obtain ⟨p,q,hp,hq,hap,hbq⟩ := empty_slot_terminal_external_neighbors M hM R hA hC hcard []
    [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr (by rw [hks]; rfl) hleft
    (c 7) (c 8) (R.coreAtom (7 : Fin 11)).2 (R.coreAtom (8 : Fin 11)).2 (hlabelc 7) (hlabelc 8)
  have hregion : ∀ z ∈ A,z=c 4 ∨ z=c 5 ∨ z=c 6 ∨ z=c 7 ∨ z=c 8 ∨
      ∃ i,1 ≤ i ∧ i ≤ kc ∧ (z=D.ladder.u i ∨ z=D.ladder.v i) := by
    intro z hz
    have hzS := hAS hz
    rcases hside z hz with h4 | h5 | h6 | h7 | h8 | hfresh
    · exact Or.inl (core_eq hzS 4 h4)
    · exact Or.inr (Or.inl (core_eq hzS 5 h5))
    · exact Or.inr (Or.inr (Or.inl (core_eq hzS 6 h6)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (core_eq hzS 7 h7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (core_eq hzS 8 h8)))))
    · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn D.ladder
        (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hzS hfresh.1 hfresh.2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,hi,hin,he⟩))))
  have h4 := D.center_mem_of_region hM hA hC hcard hregion ⟨p,hp,hap⟩
  have hfull := D.full_of_center hM hA hC hcard h4
  have h5 : c 5 ∈ A := by simpa only [D.start_upper] using (hfull 0 (by omega)).1
  have h6 : c 6 ∈ A := by simpa only [D.start_lower] using (hfull 0 (by omega)).2
  have h7 : c 7 ∈ A := by simpa only [D.end_upper] using (hfull (kc+1) le_rfl).1
  have h8 : c 8 ∈ A := by simpa only [D.end_lower] using (hfull (kc+1) le_rfl).2
  have h7j := block_joint_of_external_neighbor M hM hA h7 hp hap
  have h8j := block_joint_of_external_neighbor M hM hA h8 hq hbq
  have h78 : c 7 ≠ c 8 := by
    intro he
    have hh := congrArg R.f he
    rw [hlabelc 7,hlabelc 8] at hh
    norm_num at hh
  have hjpair : ({c 7,c 8} : Finset V)={x,y} := by
    rcases h7j with h7x | h7y <;> rcases h8j with h8x | h8y
    · exact False.elim (h78 (h7x.trans h8x.symm))
    · rw [h7x,h8y]
    · rw [h7y,h8x]
      exact pair_comm _ _
    · exact False.elim (h78 (h7y.trans h8y.symm))
  refine ⟨kr,kc,kg,hks,?_,hjpair.symm⟩
  intro z hzS
  refine ⟨hside z,?_⟩
  intro hz
  rcases hz with hz | hz | hz | hz | hz | hz
  · exact (core_eq hzS 4 hz).symm ▸ h4
  · exact (core_eq hzS 5 hz).symm ▸ h5
  · exact (core_eq hzS 6 hz).symm ▸ h6
  · exact (core_eq hzS 7 hz).symm ▸ h7
  · exact (core_eq hzS 8 hz).symm ▸ h8
  · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn D.ladder
      (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hzS hz.1 hz.2
    rcases he with rfl | rfl
    · exact (hfull i (by omega)).1
    · exact (hfull i (by omega)).2

end WaveTurbulence.Vine

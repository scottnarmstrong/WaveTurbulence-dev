/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103TwoBridgeComponents
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostBridgeCut
import Mathlib.Tactic

/-! # Actual first-star distribution in the opposite-bridge good case -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual component separation gives disjoint actual atom sets. -/
theorem componentSet_disjoint_of_not_sameComponent (M : Molecule V D) (a b : V)
    (hab : ¬ M.SameComponent a b) : Disjoint (componentSet M a) (componentSet M b) := by
  apply disjoint_left.mpr
  intro z hzA hzB
  exact hab (Relation.EqvGen.trans _ _ _ ((mem_componentSet M a z).mp hzA).2
    (Relation.EqvGen.symm _ _ ((mem_componentSet M b z).mp hzB).2))

/-- Three disjoint targets receiving a dart of a degree-three star receive
exactly one each; the complete actual star is produced, not assumed. -/
theorem exists_star_order_of_three_targets (M : Molecule V D) (v : V) (hv3 : M.deg v = 3)
    (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hA : ∃ x, M.atom x = v ∧ M.atom (M.mate x) ∈ A)
    (hB : ∃ x, M.atom x = v ∧ M.atom (M.mate x) ∈ B)
    (hC : ∃ x, M.atom x = v ∧ M.atom (M.mate x) ∈ C) :
    ∃ x y z : D, M.atom x = v ∧ M.atom y = v ∧ M.atom z = v ∧
      M.atom (M.mate x) ∈ A ∧ M.atom (M.mate y) ∈ B ∧ M.atom (M.mate z) ∈ C ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ M.dartsAt v = {x,y,z} := by
  classical
  obtain ⟨x,hx,hxA⟩ := hA
  obtain ⟨y,hy,hyB⟩ := hB
  obtain ⟨z,hz,hzC⟩ := hC
  have hxy : x ≠ y := fun h => disjoint_left.mp hAB (h ▸ hxA) hyB
  have hxz : x ≠ z := fun h => disjoint_left.mp hAC (h ▸ hxA) hzC
  have hyz : y ≠ z := fun h => disjoint_left.mp hBC (h ▸ hyB) hzC
  refine ⟨x,y,z,hx,hy,hz,hxA,hyB,hzC,hxy,hxz,hyz,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M v x).mpr hx,(Mole.mem_dartsAt M v y).mpr hy,(Mole.mem_dartsAt M v z).mpr hz⟩
  · change M.deg v ≤ _
    simp [hv3,hxy,hxz,hyz]

/-- The hard source case(3) distributes the three first-star edges one per
actual component. OLD no-beta forces the central target to receive one. -/
theorem exists_first_star_order_of_opposite_post_bridges (M : Molecule V D) (hM : M.IsMolecule)
    (hbridge : ∀ e, ¬ IsBridge M e) (hno : ¬ AdmitsBetaSplit M)
    (v : V) (hv3 : M.deg v = 3)
    (e f : RetainedDart M {v})
    (hf : f ≠ e ∧ f ≠ (eraseAtoms M {v}).mate e)
    (heB : IsBridge (eraseAtoms M {v}) e) (hfB : IsBridge (eraseAtoms M {v}) f)
    (hatom : M.atom f.val = M.atom e.val)
    (hfour : (eraseAtoms M {v}).deg (M.atom e.val) = 4)
    (hout : M.out e.val ≠ M.out f.val) :
    let N := eraseAtoms M {v}
    let P := eraseTwoBonds N e f hf
    ∃ x y z : D, M.atom x = v ∧ M.atom y = v ∧ M.atom z = v ∧
      M.atom (M.mate x) ∈ componentSet P (M.atom e.val) ∧
      M.atom (M.mate y) ∈ componentSet P (M.atom (M.mate e.val)) ∧
      M.atom (M.mate z) ∈ componentSet P (M.atom (M.mate f.val)) ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ M.dartsAt v = {x,y,z} := by
  let N := eraseAtoms M {v}
  let P := eraseTwoBonds N e f hf
  let A := componentSet P (N.atom e)
  let B := componentSet P (N.atom (N.mate e))
  let C := componentSet P (N.atom (N.mate f))
  have hbound := boundary_three_eraseTwoBonds_components N hf heB hfB hatom
  have hsep := eraseTwoBonds_three_separated N hf heB hfB hatom
  have hAsub : A ⊆ N.atoms := fun a ha => ((mem_componentSet P _ a).mp ha).1
  have hBsub : B ⊆ N.atoms := fun a ha => ((mem_componentSet P _ a).mp ha).1
  have hCsub : C ⊆ N.atoms := fun a ha => ((mem_componentSet P _ a).mp ha).1
  have hA := exists_first_edge_into_post_mixed_joint_boundary M hM hbridge hno v A hAsub e f
    hbound.1 hatom hfour hout
  have hB := exists_first_edge_into_post_single_boundary M hbridge v B hBsub (N.mate e) hbound.2.1
  have hC := exists_first_edge_into_post_single_boundary M hbridge v C hCsub (N.mate f) hbound.2.2
  exact exists_star_order_of_three_targets M v hv3 A B C
    (componentSet_disjoint_of_not_sameComponent P _ _ hsep.1)
    (componentSet_disjoint_of_not_sameComponent P _ _ hsep.2.1)
    (componentSet_disjoint_of_not_sameComponent P _ _ hsep.2.2) hA hB hC

/-- The actual opposite-bridge case supplies the precise OLD cuts used
by the five-variable source counting argument, along with its first star. -/
theorem exists_first_star_and_old_cuts_of_opposite_post_bridges (M : Molecule V D) (hM : M.IsMolecule)
    (hbridge : ∀ e, ¬ IsBridge M e) (hno : ¬ AdmitsBetaSplit M)
    (v : V) (hv3 : M.deg v = 3) (e f : RetainedDart M {v})
    (hf : f ≠ e ∧ f ≠ (eraseAtoms M {v}).mate e)
    (heB : IsBridge (eraseAtoms M {v}) e) (hfB : IsBridge (eraseAtoms M {v}) f)
    (hatom : M.atom f.val = M.atom e.val)
    (hfour : (eraseAtoms M {v}).deg (M.atom e.val) = 4)
    (hout : M.out e.val ≠ M.out f.val) :
    let N := eraseAtoms M {v}
    let P := eraseTwoBonds N e f hf
    ∃ x y z : D, M.atom x = v ∧ M.atom y = v ∧ M.atom z = v ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ M.dartsAt v = {x,y,z} ∧
      boundaryDarts M (componentSet P (M.atom e.val)) = {e.val,f.val,M.mate x} ∧
      boundaryDarts M (componentSet P (M.atom (M.mate e.val))) = {M.mate e.val,M.mate y} ∧
      boundaryDarts M (componentSet P (M.atom (M.mate f.val))) = {M.mate f.val,M.mate z} := by
  classical
  let N := eraseAtoms M {v}
  let P := eraseTwoBonds N e f hf
  let A := componentSet P (N.atom e)
  let B := componentSet P (N.atom (N.mate e))
  let C := componentSet P (N.atom (N.mate f))
  obtain ⟨x,y,z,hx,hy,hz,hxA,hyB,hzC,hxy,hxz,hyz,hstar⟩ :=
    exists_first_star_order_of_opposite_post_bridges M hM hbridge hno v hv3 e f hf heB hfB hatom hfour hout
  have hsep := eraseTwoBonds_three_separated N hf heB hfB hatom
  have hAB := componentSet_disjoint_of_not_sameComponent P _ _ hsep.1
  have hAC := componentSet_disjoint_of_not_sameComponent P _ _ hsep.2.1
  have hBC := componentSet_disjoint_of_not_sameComponent P _ _ hsep.2.2
  have hsub (a : V) : componentSet P a ⊆ N.atoms := fun b hb => ((mem_componentSet P a b).mp hb).1
  have hbound := boundary_three_eraseTwoBonds_components N hf heB hfB hatom
  have hAold := boundary_old_eq_union_first_edge_of_star M v A (hsub _) hstar hxA
    (fun h => disjoint_left.mp hAB h hyB) (fun h => disjoint_left.mp hAC h hzC)
  have hstarB : M.dartsAt v = {y,x,z} := by
    rw [hstar]
    ext w
    simp only [mem_insert,mem_singleton]
    tauto
  have hstarC : M.dartsAt v = {z,x,y} := by
    rw [hstar]
    ext w
    simp only [mem_insert,mem_singleton]
    tauto
  have hBold := boundary_old_eq_union_first_edge_of_star M v B (hsub _) hstarB hyB
    (fun h => disjoint_left.mp hAB hxA h) (fun h => disjoint_left.mp hBC h hzC)
  have hCold := boundary_old_eq_union_first_edge_of_star M v C (hsub _) hstarC hzC
    (fun h => disjoint_left.mp hAC hxA h) (fun h => disjoint_left.mp hBC hyB h)
  rw [hbound.1,image_insert,image_singleton] at hAold
  rw [hbound.2.1,image_singleton] at hBold
  rw [hbound.2.2,image_singleton] at hCold
  change boundaryDarts M B = {M.mate e.val} ∪ {M.mate y} at hBold
  change boundaryDarts M C = {M.mate f.val} ∪ {M.mate z} at hCold
  refine ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz,hstar,?_,?_,?_⟩
  · change boundaryDarts M A = {e.val,f.val,M.mate x}
    rw [hAold]
    ext w
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  · change boundaryDarts M B = {M.mate e.val,M.mate y}
    rw [hBold]
    ext w
    simp only [mem_union,mem_insert,mem_singleton]
  · change boundaryDarts M C = {M.mate f.val,M.mate z}
    rw [hCold]
    ext w
    simp only [mem_union,mem_insert,mem_singleton]

end WaveTurbulence.MoleProp

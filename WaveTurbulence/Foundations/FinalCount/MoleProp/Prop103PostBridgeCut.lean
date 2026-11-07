/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103OrdinaryStep
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaCut
import Mathlib.Tactic

/-! # An actual newly created bridge supplies the source two-label cut -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Old boundary darts either survive or end at the removed atom. -/
theorem boundary_old_subset_of_post_single_boundary (M : Molecule V D) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms)
    (q : RetainedDart M {v}) (hboundary : boundaryDarts (eraseAtoms M {v}) S = {q}) :
    q.val ∈ boundaryDarts M S ∧ boundaryDarts M S ⊆
      {q.val} ∪ ((M.dartsAt v).image M.mate) := by
  classical
  constructor
  · have hq : q ∈ boundaryDarts (eraseAtoms M {v}) S := by rw [hboundary]; simp
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hq).2⟩
  · intro z hz
    have hh := (mem_filter.mp hz).2
    by_cases hmv : M.atom (M.mate z) = v
    · apply mem_union_right
      apply mem_image.mpr
      exact ⟨M.mate z,(Mole.mem_dartsAt M v _).mpr hmv,M.mate_mate z⟩
    · apply mem_union_left
      have hzv : M.atom z ∉ ({v} : Finset V) := (mem_sdiff.mp (hS hh.1)).2
      let z' : RetainedDart M {v} := ⟨z,hzv,by simpa only [mem_singleton] using hmv⟩
      have hz' : z' ∈ boundaryDarts (eraseAtoms M {v}) S := mem_filter.mpr ⟨mem_univ _,hh⟩
      rw [hboundary] at hz'
      exact mem_singleton.mpr (congrArg Subtype.val (mem_singleton.mp hz'))

/-- Every post-R bridge leaf receives an actual first-star edge, since
otherwise it would already be an OLD bridge cut. -/
theorem exists_first_edge_into_post_single_boundary (M : Molecule V D)
    (hbridge : ∀ e, ¬ IsBridge M e) (v : V) (S : Finset V)
    (hS : S ⊆ (eraseAtoms M {v}).atoms) (q : RetainedDart M {v})
    (hq : boundaryDarts (eraseAtoms M {v}) S = {q}) :
    ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) ∈ S := by
  classical
  have hh := boundary_old_subset_of_post_single_boundary M v S hS q hq
  have hlo := two_le_boundary_card M hbridge S ⟨q.val,hh.1⟩
  have hpos : ((boundaryDarts M S).erase q.val).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hh.1]
    omega
  obtain ⟨z,hz⟩ := hpos
  have hz' := mem_erase.mp hz
  have hzm : z ∈ (M.dartsAt v).image M.mate := by
    rcases mem_union.mp (hh.2 hz'.2) with h | h
    · exact False.elim (hz'.1 (mem_singleton.mp h))
    · exact h
  obtain ⟨p,hp,hpz⟩ := mem_image.mp hzm
  exact ⟨p,(Mole.mem_dartsAt M v p).mp hp,hpz.symm ▸ (mem_filter.mp hz'.2).2.1⟩

/-- A bridge created by removing a degree-three atom always has one side
with exactly two OLD boundary bonds. No assumption identifies its first
star label with a distinct label at the second atom. -/
theorem exists_old_two_boundary_side_of_post_bridge (M : Molecule V D)
    (hbridge : ∀ e, ¬ IsBridge M e) (v : V) (hv3 : M.deg v = 3)
    (e : RetainedDart M {v}) (he : IsBridge (eraseAtoms M {v}) e) :
    ∃ (S : Finset V) (q : RetainedDart M {v}),
      S ⊆ (eraseAtoms M {v}).atoms ∧ (q = e ∨ q = (eraseAtoms M {v}).mate e) ∧
      boundaryDarts (eraseAtoms M {v}) S = {q} ∧ (boundaryDarts M S).card = 2 := by
  classical
  let N := eraseAtoms M {v}
  let S := bridgeSide N e
  let T := N.atoms \ S
  have hS : S ⊆ N.atoms := bridgeSide_subset N e
  have hT : T ⊆ N.atoms := sdiff_subset
  have hbS : boundaryDarts N S = {e} := boundary_bridgeSide N e he
  have hbT : boundaryDarts N T = {N.mate e} := by
    rw [boundary_atoms_sdiff_eq_image_mate N S,hbS,image_singleton]
  have hOldS := boundary_old_subset_of_post_single_boundary M v S hS e hbS
  have hOldT := boundary_old_subset_of_post_single_boundary M v T hT (N.mate e) hbT
  have hloS := two_le_boundary_card M hbridge S ⟨e.val,hOldS.1⟩
  have hloT := two_le_boundary_card M hbridge T ⟨(N.mate e).val,hOldT.1⟩
  have hdis : Disjoint (boundaryDarts M S) (boundaryDarts M T) := by
    apply disjoint_left.mpr
    intro z hzS hzT
    have hzS' := (mem_filter.mp hzS).2.1
    have hzT' := (mem_filter.mp hzT).2.1
    exact (mem_sdiff.mp hzT').2 hzS'
  have hsub : boundaryDarts M S ∪ boundaryDarts M T ⊆
      {e.val,M.mate e.val} ∪ (M.dartsAt v).image M.mate := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · rcases mem_union.mp (hOldS.2 hz) with hz | hz
      · exact mem_union_left _ (mem_insert.mpr (Or.inl (mem_singleton.mp hz)))
      · exact mem_union_right _ hz
    · rcases mem_union.mp (hOldT.2 hz) with hz | hz
      · have hz' := mem_singleton.mp hz
        change z = M.mate e.val at hz'
        exact mem_union_left _ (mem_insert.mpr (Or.inr (mem_singleton.mpr hz')))
      · exact mem_union_right _ hz
  have hcard : (boundaryDarts M S).card + (boundaryDarts M T).card ≤ 5 := by
    have hh := card_le_card hsub
    rw [card_union_of_disjoint hdis] at hh
    have hu := card_union_le ({e.val,M.mate e.val}) ((M.dartsAt v).image M.mate)
    have hp := card_pair (Ne.symm (M.mate_ne e.val))
    have hi := card_image_le (s := M.dartsAt v) (f := M.mate)
    change (M.dartsAt v).card = 3 at hv3
    omega
  by_cases hcS : (boundaryDarts M S).card = 2
  · exact ⟨S,e,hS,Or.inl rfl,hbS,hcS⟩
  · have hcT : (boundaryDarts M T).card = 2 := by omega
    exact ⟨T,N.mate e,hT,Or.inr rfl,hbT,hcT⟩

/-- The old two-bond cut contains exactly the surviving bridge and one
actual bond at the first removed atom. This label is allowed to be the
old edge joining the two removed atoms. -/
theorem old_two_boundary_eq_bridge_and_first_edge (M : Molecule V D) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms)
    (q : RetainedDart M {v}) (hq : boundaryDarts (eraseAtoms M {v}) S = {q})
    (hcard : (boundaryDarts M S).card = 2) :
    ∃ p : D, M.atom p = v ∧ boundaryDarts M S = {q.val,M.mate p} ∧ q.val ≠ M.mate p := by
  classical
  have hh := boundary_old_subset_of_post_single_boundary M v S hS q hq
  have hpos : ((boundaryDarts M S).erase q.val).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hh.1,hcard]
    decide
  obtain ⟨z,hz⟩ := hpos
  obtain ⟨hzq,hz⟩ := mem_erase.mp hz
  have hzm : z ∈ (M.dartsAt v).image M.mate := by
    rcases mem_union.mp (hh.2 hz) with h | h
    · exact False.elim (hzq (mem_singleton.mp h))
    · exact h
  obtain ⟨p,hp,hpz⟩ := mem_image.mp hzm
  refine ⟨p,(Mole.mem_dartsAt M v p).mp hp,?_,?_⟩
  · have hs : {q.val,M.mate p} ⊆ boundaryDarts M S := by
      intro t ht
      simp only [mem_insert,mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hh.1
      · exact hpz.symm ▸ hz
    symm
    apply Finset.eq_of_subset_of_card_le hs
    rw [hcard]
    have hne : q.val ≠ M.mate p := fun h => hzq (hpz.symm.trans h.symm)
    rw [card_pair hne]
  · intro h
    exact hzq (hpz.symm.trans h.symm)

/-- If a retained side receives no first-star edge, its OLD boundary is
exactly its actual post-R boundary, with the dart subtype forgotten. -/
theorem boundary_old_eq_image_of_no_first_edge (M : Molecule V D) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms)
    (hnone : ∀ p, M.atom p = v → M.atom (M.mate p) ∉ S) :
    boundaryDarts M S = (boundaryDarts (eraseAtoms M {v}) S).image (fun z => z.val) := by
  classical
  ext z
  constructor
  · intro hz
    have hh := (mem_filter.mp hz).2
    have hzv := (mem_sdiff.mp (hS hh.1)).2
    have hmv : M.atom (M.mate z) ∉ ({v} : Finset V) := by
      intro h
      have hv : M.atom (M.mate z) = v := by simpa only [mem_singleton] using h
      exact hnone (M.mate z) hv (by simpa only [M.mate_mate] using hh.1)
    exact mem_image.mpr ⟨⟨z,hzv,hmv⟩,mem_filter.mpr ⟨mem_univ _,hh⟩,rfl⟩
  · intro hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩

/-- In the hard opposite-bridge case, the central component must receive
an actual first-star edge. Otherwise its OLD mixed boundary enables beta. -/
theorem exists_first_edge_into_post_mixed_joint_boundary (M : Molecule V D) (hM : M.IsMolecule)
    (hbridge : ∀ e, ¬ IsBridge M e) (hno : ¬ AdmitsBetaSplit M) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms)
    (q r : RetainedDart M {v})
    (hq : boundaryDarts (eraseAtoms M {v}) S = {q,r})
    (hatom : M.atom r.val = M.atom q.val)
    (hfour : (eraseAtoms M {v}).deg (M.atom q.val) = 4)
    (hout : M.out q.val ≠ M.out r.val) :
    ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) ∈ S := by
  classical
  by_contra hn
  push Not at hn
  have hb := boundary_old_eq_image_of_no_first_edge M v S hS hn
  rw [hq,image_insert,image_singleton] at hb
  have hbOld : M.deg (M.atom q.val) = 4 := by
    have hh := deg_eraseAtoms_add_removed M {v} q.property.1
    have hc := Mole.deg_le_four M hM (M.atom_mem q.val)
    omega
  have heq := out_eq_of_joint_two_boundary_no_beta M hbOld rfl hatom
    (fun e _ => hbridge e) hno S hb
  exact hout heq

/-- Exactly one first-star edge enters the retained side, so its OLD
boundary is the actual surviving boundary plus that one deleted edge. -/
theorem boundary_old_eq_union_one_first_edge (M : Molecule V D) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms)
    (p : D) (hp : M.atom p = v) (hpS : M.atom (M.mate p) ∈ S)
    (honly : ∀ q, M.atom q = v → M.atom (M.mate q) ∈ S → q = p) :
    boundaryDarts M S = (boundaryDarts (eraseAtoms M {v}) S).image (fun z => z.val) ∪ {M.mate p} := by
  classical
  have hvnot : v ∉ S := fun h => (mem_sdiff.mp (hS h)).2 (mem_singleton_self v)
  ext z
  constructor
  · intro hz
    have hh := (mem_filter.mp hz).2
    by_cases hmv : M.atom (M.mate z) = v
    · apply mem_union_right
      apply mem_singleton.mpr
      have hmz := honly (M.mate z) hmv (by simpa only [M.mate_mate] using hh.1)
      simpa only [M.mate_mate] using congrArg M.mate hmz
    · apply mem_union_left
      have hzv := (mem_sdiff.mp (hS hh.1)).2
      exact mem_image.mpr ⟨⟨z,hzv,by simpa only [mem_singleton] using hmv⟩,
        mem_filter.mpr ⟨mem_univ _,hh⟩,rfl⟩
  · intro hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    · have he := mem_singleton.mp hz
      subst z
      exact mem_filter.mpr ⟨mem_univ _,hpS,by simpa only [M.mate_mate,hp] using hvnot⟩

/-- The produced complete first star and the target memberships establish
that only its selected edge enters this actual retained side. -/
theorem boundary_old_eq_union_first_edge_of_star (M : Molecule V D) (v : V)
    (S : Finset V) (hS : S ⊆ (eraseAtoms M {v}).atoms) {x y z : D}
    (hstar : M.dartsAt v = {x,y,z}) (hxS : M.atom (M.mate x) ∈ S)
    (hyS : M.atom (M.mate y) ∉ S) (hzS : M.atom (M.mate z) ∉ S) :
    boundaryDarts M S = (boundaryDarts (eraseAtoms M {v}) S).image (fun q => q.val) ∪ {M.mate x} := by
  have hx : M.atom x = v := (Mole.mem_dartsAt M v x).mp (by rw [hstar]; simp)
  apply boundary_old_eq_union_one_first_edge M v S hS x hx hxS
  intro q hq hqS
  have hqm : q ∈ M.dartsAt v := (Mole.mem_dartsAt M v q).mpr hq
  rw [hstar] at hqm
  simp only [mem_insert,mem_singleton] at hqm
  rcases hqm with h | h | h
  · exact h
  · exact False.elim (hyS (h ▸ hqS))
  · exact False.elim (hzS (h ▸ hqS))

/-- When the chosen bridge side contains the local joint, its single
boundary dart is the bridge dart AT that joint, not its mate. -/
theorem single_boundary_bridge_dart_eq_of_joint_mem (M : Molecule V D)
    (S : Finset V) {e q : D} (hq : boundaryDarts M S = {q})
    (hcases : q = e ∨ q = M.mate e) (heS : M.atom e ∈ S) : q = e := by
  rcases hcases with h | h
  · exact h
  · have hqm : q ∈ boundaryDarts M S := by rw [hq]; simp
    have hn := (mem_filter.mp hqm).2.2
    rw [h,M.mate_mate] at hn
    exact False.elim (hn heS)

/-- A surviving four-star retained the entire old star. -/
theorem old_star_eq_image_of_eraseAtoms_four (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) {b : V} (hb : b ∈ M.atoms) (h4 : (eraseAtoms M Y).deg b = 4) :
    ((eraseAtoms M Y).dartsAt b).image (fun z => z.val) = M.dartsAt b := by
  classical
  have hs : ((eraseAtoms M Y).dartsAt b).image (fun z => z.val) ⊆ M.dartsAt b := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact (Mole.mem_dartsAt M b x.val).mpr ((Mole.mem_dartsAt _ b x).mp hx)
  apply Finset.eq_of_subset_of_card_le hs
  rw [card_image_of_injective _ Subtype.val_injective]
  change M.deg b ≤ (eraseAtoms M Y).deg b
  rw [h4]
  exact Mole.deg_le_four M hM hb

/-- No first-star edge can end at a vertex whose post-R degree is four. -/
theorem first_edge_ne_surviving_four (M : Molecule V D) (hM : M.IsMolecule) (v : V)
    (q : RetainedDart M {v}) (h4 : (eraseAtoms M {v}).deg (M.atom q.val) = 4)
    {p : D} (hp : M.atom p = v) : M.atom (M.mate p) ≠ M.atom q.val := by
  intro h
  have hAdj : M.Adj (M.atom q.val) v := ⟨M.mate p,h,by rw [M.mate_mate,hp]⟩
  have hh := adj_erase_of_surviving_four M hM {v} ((eraseAtoms M {v}).atom_mem q) h4 hAdj
  exact (mem_sdiff.mp hh.1).2 (mem_singleton_self v)

/-- Each side of an actual post-R mixed pair cut receives a first-star
edge, or else the same cut would already enable beta in the OLD graph. -/
theorem exists_first_edge_into_post_mixed_pair_side (M : Molecule V D) (hM : M.IsMolecule)
    (hbridge : ∀ e, ¬ IsBridge M e) (hno : ¬ AdmitsBetaSplit M) (v : V)
    (x y : RetainedDart M {v}) (hatom : M.atom y.val = M.atom x.val)
    (h4 : (eraseAtoms M {v}).deg (M.atom x.val) = 4)
    (hxo : M.out x.val = false) (hyo : M.out y.val = true)
    (U : Finset V) (hU : U ⊆ (eraseAtoms M {v}).atoms \ {M.atom x.val})
    (hcut : boundaryDarts (eraseAtoms M {v}) U = {(eraseAtoms M {v}).mate x,(eraseAtoms M {v}).mate y}) :
    ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) ∈ U := by
  classical
  by_contra hn
  push Not at hn
  have hb := boundary_old_eq_image_of_no_first_edge M v U
    (fun a ha => (mem_sdiff.mp (hU ha)).1) hn
  rw [hcut,image_insert,image_singleton] at hb
  have hOld4 : M.deg (M.atom x.val) = 4 := by
    have hh := deg_eraseAtoms_add_removed M {v} x.property.1
    have hc := Mole.deg_le_four M hM (M.atom_mem x.val)
    omega
  have hUold : U ⊆ M.atoms \ {M.atom x.val} := by
    intro a ha
    have hh := mem_sdiff.mp (hU ha)
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hh.1).1,hh.2⟩
  exact hno (admitsBetaSplit_of_old_mixed_cut M (M.atom_mem x.val) hOld4 rfl hatom hxo hyo
    (fun e _ => hbridge e) U hUold hb)

end WaveTurbulence.MoleProp

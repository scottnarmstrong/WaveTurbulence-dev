/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeSeparation
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairCircuit
import Mathlib.Tactic

/-! # Actual bridge deletion for the Proposition 10.3 search -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Keep both darts of every undirected bond other than the selected one. -/
abbrev WithoutBondDart (M : Molecule V D) (e : D) := {x : D // x ≠ e ∧ x ≠ M.mate e}

/-- Source operation B: remove one undirected bond and keep every atom. -/
def eraseBond (M : Molecule V D) (e : D) : Molecule V (WithoutBondDart M e) where
  atoms := M.atoms
  atom x := M.atom x.val
  mate x := ⟨M.mate x.val,by
    constructor
    · intro h
      apply x.property.2
      have hh := congrArg M.mate h
      simpa only [M.mate_mate] using hh
    · intro h
      exact x.property.1 (Mole.mate_injective M h)⟩
  out x := M.out x.val
  atom_mem x := M.atom_mem x.val
  mate_mate x := Subtype.ext (M.mate_mate x.val)
  mate_ne x h := M.mate_ne x.val (congrArg Subtype.val h)
  out_mate x := M.out_mate x.val

theorem eraseBond_adj_iff (M : Molecule V D) (e : D) (a b : V) :
    (eraseBond M e).Adj a b ↔ AdjWithoutBond M e a b := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    exact ⟨x.val,hx,hxm,x.property⟩
  · rintro ⟨x,hx,hxm,hxe,hxmE⟩
    exact ⟨⟨x,hxe,hxmE⟩,hx,hxm⟩

theorem eraseBond_sameComponent_iff (M : Molecule V D) (e : D) (a b : V) :
    (eraseBond M e).SameComponent a b ↔ Relation.EqvGen (AdjWithoutBond M e) a b :=
  ⟨fun h => Relation.EqvGen.mono (fun u v h => (eraseBond_adj_iff M e u v).mp h) a b h,
    fun h => Relation.EqvGen.mono (fun u v h => (eraseBond_adj_iff M e u v).mpr h) a b h⟩

/-- Complementary cuts have mate boundary darts, including unrelated old components. -/
theorem boundary_atoms_sdiff_eq_image_mate (M : Molecule V D) (S : Finset V) :
    boundaryDarts M (M.atoms \ S) = (boundaryDarts M S).image M.mate := by
  ext x
  constructor
  · intro hx
    have hxa := (mem_filter.mp hx).2.1
    have hxma := (mem_filter.mp hx).2.2
    have hxmS : M.atom (M.mate x) ∈ S := by
      by_contra hn
      exact hxma (mem_sdiff.mpr ⟨M.atom_mem _,hn⟩)
    exact mem_image.mpr ⟨M.mate x,mem_filter.mpr ⟨mem_univ _,hxmS,
      by simpa only [M.mate_mate] using (mem_sdiff.mp hxa).2⟩,M.mate_mate x⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hyS := (mem_filter.mp hy).2.1
    have hymS := (mem_filter.mp hy).2.2
    apply mem_filter.mpr
    refine ⟨mem_univ _,mem_sdiff.mpr ⟨M.atom_mem _,hymS⟩,?_⟩
    intro hh
    exact (mem_sdiff.mp hh).2 (by simpa only [M.mate_mate] using hyS)

private theorem singleton_boundary_dart_mem (M : Molecule V D) {S : Finset V} {z : D}
    (hcut : boundaryDarts M S = {z}) : M.atom z ∈ S ∧ M.atom (M.mate z) ∉ S := by
  have hh : z ∈ boundaryDarts M S := by rw [hcut]; exact mem_singleton_self _
  exact (mem_filter.mp hh).2

private theorem path_withoutBond_restrict_to_cut_side (M : Molecule V D) (e : D)
    (f : WithoutBondDart M e) (S : Finset V) (z : D) (hcut : boundaryDarts M S = {z})
    (hz : z = e ∨ z = M.mate e) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (hp : Relation.EqvGen (AdjWithoutBond M f.val) u v) :
    Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) u v := by
  classical
  have hends := singleton_boundary_dart_mem M hcut
  have hcross (x : D) (hx : M.atom x ∈ S) (hxm : M.atom (M.mate x) ∉ S) : x = z := by
    have hh : x ∈ boundaryDarts M S := mem_filter.mpr ⟨mem_univ _,hx,hxm⟩
    rw [hcut] at hh
    exact mem_singleton.mp hh
  have hnotBoth : ¬(M.atom e ∈ S ∧ M.atom (M.mate e) ∈ S) := by
    rintro ⟨ha,hb⟩
    rcases hz with hz | hz
    · exact hends.2 (by rw [hz]; exact hb)
    · exact hends.2 (by rw [hz,M.mate_mate]; exact ha)
  have hInternal {a b : V} (ha : a ∈ S) (hb : b ∈ S) (h : AdjWithoutBond M f.val a b) :
      AdjWithoutBond (eraseBond M e) f a b := by
    obtain ⟨x,hx,hxm,hxf,hxfm⟩ := h
    have hxS : M.atom x ∈ S := hx.symm ▸ ha
    have hxmS : M.atom (M.mate x) ∈ S := hxm.symm ▸ hb
    have hxe : x ≠ e := by intro h; exact hnotBoth ⟨h ▸ hxS,h ▸ hxmS⟩
    have hxme : x ≠ M.mate e := by
      intro h
      have hleft : M.atom (M.mate e) ∈ S := h ▸ hxS
      have hright : M.atom e ∈ S := by simpa only [h,M.mate_mate] using hxmS
      exact hnotBoth ⟨hright,hleft⟩
    refine ⟨⟨x,hxe,hxme⟩,hx,hxm,?_,?_⟩
    · intro hh; exact hxf (congrArg Subtype.val hh)
    · intro hh; exact hxfm (congrArg Subtype.val hh)
  let R := fun a => if a ∈ S then a else M.atom z
  have hstep (a b : V) (h : AdjWithoutBond M f.val a b) :
      Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) (R a) (R b) := by
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · simpa only [R,ite_eq_left ha,ite_eq_left hb] using Relation.EqvGen.rel _ _ (hInternal ha hb h)
      · obtain ⟨x,hx,hxm,_hxf,_hxfm⟩ := h
        have hxe := hcross x (hx.symm ▸ ha) (hxm.symm ▸ hb)
        have haroot : a = M.atom z := hx.symm.trans (congrArg M.atom hxe)
        simpa only [R,ite_eq_left ha,ite_eq_right hb,haroot,ite_self] using
          (Relation.EqvGen.refl (M.atom z) : Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) _ _)
    · by_cases hb : b ∈ S
      · obtain ⟨x,hx,hxm,_hxf,_hxfm⟩ := h
        have hxe := hcross (M.mate x) (hxm.symm ▸ hb) (by simpa only [M.mate_mate,hx] using ha)
        have hbroot : b = M.atom z := hxm.symm.trans (congrArg M.atom hxe)
        simpa only [R,ite_eq_right ha,ite_eq_left hb,hbroot,ite_self] using
          (Relation.EqvGen.refl (M.atom z) : Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) _ _)
      · simpa only [R,ite_eq_right ha,ite_eq_right hb] using
          (Relation.EqvGen.refl (M.atom z) : Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) _ _)
  have hmap (a b : V) (h : Relation.EqvGen (AdjWithoutBond M f.val) a b) :
      Relation.EqvGen (AdjWithoutBond (eraseBond M e) f) (R a) (R b) := by
    induction h with
    | rel a b h => exact hstep a b h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  simpa only [R,ite_eq_left hu,ite_eq_left hv] using hmap u v hp

/-- DH23 L1916: deleting one actual bridge cannot change whether any
other surviving actual bond is a bridge. -/
theorem isBridge_eraseBond_iff (M : Molecule V D) (e : D) (he : IsBridge M e)
    (f : WithoutBondDart M e) : IsBridge (eraseBond M e) f ↔ IsBridge M f.val := by
  classical
  have hcut := boundary_bridgeSide M e he
  let S := bridgeSide M e
  have hcross (x : D) (hx : M.atom x ∈ S) (hxm : M.atom (M.mate x) ∉ S) : x = e := by
    have hh : x ∈ boundaryDarts M S := mem_filter.mpr ⟨mem_univ _,hx,hxm⟩
    rw [hcut] at hh
    exact mem_singleton.mp hh
  have hiff : M.atom f.val ∈ S ↔ M.atom (M.mate f.val) ∈ S := by
    constructor
    · intro hin
      by_contra hout
      exact f.property.1 (hcross f.val hin hout)
    · intro hin
      by_contra hout
      have hm := hcross (M.mate f.val) hin (by simpa only [M.mate_mate] using hout)
      have hh := congrArg M.mate hm
      rw [M.mate_mate] at hh
      exact f.property.2 hh
  constructor
  · intro hn
    by_contra ho
    have hp : Relation.EqvGen (AdjWithoutBond M f.val) (M.atom f.val) (M.atom (M.mate f.val)) := by
      by_contra hp
      exact ho hp
    apply hn
    by_cases hin : M.atom f.val ∈ S
    · exact path_withoutBond_restrict_to_cut_side M e f S e hcut (Or.inl rfl) hin (hiff.mp hin) hp
    · have hcomp : boundaryDarts M (M.atoms \ S) = {M.mate e} := by
        rw [boundary_atoms_sdiff_eq_image_mate,hcut,image_singleton]
      exact path_withoutBond_restrict_to_cut_side M e f (M.atoms \ S) (M.mate e) hcomp (Or.inr rfl)
        (mem_sdiff.mpr ⟨M.atom_mem _,hin⟩)
        (mem_sdiff.mpr ⟨M.atom_mem _,fun h => hin (hiff.mpr h)⟩) hp
  · intro ho hn
    apply ho
    have hLift : AdjWithoutBond (eraseBond M e) f ≤ AdjWithoutBond M f.val := by
      rintro a b ⟨x,hx,hxm,hxf,hxfm⟩
      refine ⟨x.val,hx,hxm,?_,?_⟩
      · intro h; exact hxf (Subtype.ext h)
      · intro h; exact hxfm (Subtype.ext h)
    exact Relation.EqvGen.mono hLift _ _ hn

end WaveTurbulence.MoleProp

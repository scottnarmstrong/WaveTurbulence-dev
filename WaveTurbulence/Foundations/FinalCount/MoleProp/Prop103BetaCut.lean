/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaState
import Mathlib.Tactic

/-! # An actual permitted beta split supplies the old mixed two-bond cut -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Darts away from the split atom retain their old embedded endpoint. -/
theorem fresh_cut_atom_of_ne (M : Molecule V D) (v : V) (x y z : D)
    (hz : M.atom z ≠ v) :
    ((withFreshAtom M).cut (some v) none x y).atom z = some (M.atom z) := by
  change (if some (M.atom z) = some v ∧ z ≠ x ∧ z ≠ y then none else some (M.atom z)) = _
  simp [hz]

/-- The selected darts stay at the kept joint. -/
theorem fresh_cut_atom_left (M : Molecule V D) {v : V} {x y : D}
    (hx : M.atom x = v) :
    ((withFreshAtom M).cut (some v) none x y).atom x = some v := by
  change (if some (M.atom x) = some v ∧ x ≠ x ∧ x ≠ y then none else some (M.atom x)) = _
  simp [hx]

theorem fresh_cut_atom_right (M : Molecule V D) {v : V} {x y : D}
    (hy : M.atom y = v) :
    ((withFreshAtom M).cut (some v) none x y).atom y = some v := by
  change (if some (M.atom y) = some v ∧ y ≠ x ∧ y ≠ y then none else some (M.atom y)) = _
  simp [hy]

/-- The kept beta component, with its new degree-two joint removed, is a
literal OLD atom set whose boundary consists of the two selected bonds.
This supplies fixed old cut equations for the direct degree-four deletion. -/
theorem exists_old_cut_of_beta_split (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    {v : V} {x y : D}
    (hx : M.atom x = v) (hy : M.atom y = v)
    (hdisc : ¬ ((withFreshAtom M).cut (some v) none x y).SameComponent (some v) none) :
    ∃ U : Finset V, U ⊆ M.atoms \ {v} ∧
      boundaryDarts M U = {M.mate x,M.mate y} ∧
      M.atom (M.mate x) ∈ U ∧ M.atom (M.mate y) ∈ U := by
  classical
  let C := (withFreshAtom M).cut (some v) none x y
  let U := M.atoms.filter (fun a => a ≠ v ∧ C.SameComponent (some v) (some a))
  have hmem (a : V) : a ∈ U ↔ a ∈ M.atoms ∧ a ≠ v ∧ C.SameComponent (some v) (some a) := by
    exact mem_filter
  have hleft : C.atom x = some v := fresh_cut_atom_left M hx
  have hright : C.atom y = some v := fresh_cut_atom_right M hy
  have hnx : M.atom (M.mate x) ≠ v := fun h => hloop x (hx.trans h.symm)
  have hny : M.atom (M.mate y) ≠ v := fun h => hloop y (hy.trans h.symm)
  have hxm : M.atom (M.mate x) ∈ U := by
    apply (hmem _).mpr
    refine ⟨M.atom_mem _,hnx,Relation.EqvGen.rel _ _ ⟨x,hleft,?_⟩⟩
    exact fresh_cut_atom_of_ne M v x y (M.mate x) hnx
  have hym : M.atom (M.mate y) ∈ U := by
    apply (hmem _).mpr
    refine ⟨M.atom_mem _,hny,Relation.EqvGen.rel _ _ ⟨y,hright,?_⟩⟩
    exact fresh_cut_atom_of_ne M v x y (M.mate y) hny
  have hvnot : v ∉ U := fun h => ((hmem v).mp h).2.1 rfl
  refine ⟨U,?_,?_,hxm,hym⟩
  · intro a ha
    have hh := (hmem a).mp ha
    exact mem_sdiff.mpr ⟨hh.1,by simpa only [mem_singleton] using hh.2.1⟩
  · ext z
    simp only [boundaryDarts,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    constructor
    · intro hz
      have hza := (hmem _).mp hz.1
      have hcz : C.atom z = some (M.atom z) := fresh_cut_atom_of_ne M v x y z hza.2.1
      have hp : C.SameComponent (some v) (C.atom (M.mate z)) :=
        Relation.EqvGen.trans _ _ _ hza.2.2 (Relation.EqvGen.rel _ _ ⟨z,hcz,rfl⟩)
      have hmz : M.atom (M.mate z) = v := by
        by_contra hn
        have hc := fresh_cut_atom_of_ne M v x y (M.mate z) hn
        apply hz.2
        exact (hmem _).mpr ⟨M.atom_mem _,hn,hc ▸ hp⟩
      have hsel : M.mate z = x ∨ M.mate z = y := by
        by_contra hn
        push Not at hn
        have hc : C.atom (M.mate z) = none := by
          change (if some (M.atom (M.mate z)) = some v ∧ M.mate z ≠ x ∧ M.mate z ≠ y
            then none else some (M.atom (M.mate z))) = none
          simp [hmz,hn.1,hn.2]
        apply hdisc
        change C.SameComponent (some v) none
        rwa [hc] at hp
      rcases hsel with h | h
      · left
        have hh := congrArg M.mate h
        simpa only [M.mate_mate] using hh
      · right
        have hh := congrArg M.mate h
        simpa only [M.mate_mate] using hh
    · rintro (rfl | rfl)
      · exact ⟨hxm,by simpa only [M.mate_mate,hx] using hvnot⟩
      · exact ⟨hym,by simpa only [M.mate_mate,hy] using hvnot⟩

/-- Conversely, an actual old two-bond side attached through the selected
pair disconnects the two literal split joints. -/
theorem beta_split_disconnected_of_old_cut (M : Molecule V D) {v : V} {x y : D}
    (hx : M.atom x = v) (hy : M.atom y = v)
    (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hboundary : boundaryDarts M U = {M.mate x,M.mate y}) :
    ¬ ((withFreshAtom M).cut (some v) none x y).SameComponent (some v) none := by
  classical
  let C := (withFreshAtom M).cut (some v) none x y
  let P : Option V → Prop := fun a => a = some v ∨ ∃ u ∈ U, a = some u
  have hvnot : v ∉ U := fun h => (mem_sdiff.mp (hU h)).2 (mem_singleton_self v)
  have hxm : M.atom (M.mate x) ∈ U := by
    have hh : M.mate x ∈ boundaryDarts M U := by rw [hboundary]; simp
    exact (mem_filter.mp hh).2.1
  have hym : M.atom (M.mate y) ∈ U := by
    have hh : M.mate y ∈ boundaryDarts M U := by rw [hboundary]; simp
    exact (mem_filter.mp hh).2.1
  have hpz (z : D) : P (C.atom z) ↔ M.atom z ∈ U ∨ z = x ∨ z = y := by
    by_cases hzx : z = x
    · subst z
      rw [fresh_cut_atom_left M hx]
      simp [P]
    by_cases hzy : z = y
    · subst z
      rw [fresh_cut_atom_right M hy]
      simp [P]
    by_cases hzv : M.atom z = v
    · have hc : C.atom z = none := by
        change (if some (M.atom z) = some v ∧ z ≠ x ∧ z ≠ y then none else some (M.atom z)) = none
        simp [hzv,hzx,hzy]
      rw [hc]
      simp [P,hzv,hvnot,hzx,hzy]
    · rw [fresh_cut_atom_of_ne M v x y z hzv]
      simp [P,hzv,hzx,hzy]
  have hpmate (z : D) (hz : P (C.atom z)) : P (C.atom (M.mate z)) := by
    apply (hpz _).mpr
    rcases (hpz z).mp hz with hzu | rfl | rfl
    · by_cases hmu : M.atom (M.mate z) ∈ U
      · exact Or.inl hmu
      · have hb : z ∈ boundaryDarts M U := mem_filter.mpr ⟨mem_univ _,hzu,hmu⟩
        rw [hboundary] at hb
        simp only [mem_insert,mem_singleton] at hb
        rcases hb with hb | hb
        · exact Or.inr (Or.inl (by simpa only [M.mate_mate] using congrArg M.mate hb))
        · exact Or.inr (Or.inr (by simpa only [M.mate_mate] using congrArg M.mate hb))
    · exact Or.inl hxm
    · exact Or.inl hym
  have hstep (a b : Option V) (hab : C.Adj a b) : P a ↔ P b := by
    obtain ⟨z,hza,hzb⟩ := hab
    constructor
    · intro ha
      have hh := hpmate z (hza.symm ▸ ha)
      exact hzb ▸ hh
    · intro hb
      have hh := hpmate (M.mate z) (hzb.symm ▸ hb)
      simpa only [M.mate_mate,hza] using hh
  have hpath (a b : Option V) (hp : C.SameComponent a b) : P a ↔ P b := by
    induction hp with
    | rel a b h => exact hstep a b h
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  intro hp
  have hh := (hpath (some v) none hp).mp (Or.inl rfl)
  simpa [P] using hh

/-- Actual mixed old-cut data is a source beta operation whenever the
standing graph requirements hold. -/
theorem admitsBetaSplit_of_old_mixed_cut (M : Molecule V D) {v : V} {x y : D}
    (hv : v ∈ M.atoms) (hv4 : M.deg v = 4)
    (hx : M.atom x = v) (hy : M.atom y = v)
    (hxo : M.out x = false) (hyo : M.out y = true)
    (hbridge : ∀ e, M.atom e = v → ¬ IsBridge M e)
    (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hboundary : boundaryDarts M U = {M.mate x,M.mate y}) : AdmitsBetaSplit M := by
  have hxy : y ≠ M.mate x := by
    intro h
    have hm : M.mate x ∈ boundaryDarts M U := by rw [hboundary]; simp
    have hmem : M.atom (M.mate x) ∈ U := (mem_filter.mp hm).2.1
    have hnv := (mem_sdiff.mp (hU hmem)).2
    exact hnv (by simp only [mem_singleton]; exact (congrArg M.atom h).symm.trans hy)
  exact ⟨v,x,y,isCutData_withFreshAtom M hv hx hy hxy hxo hyo,hv4,hbridge,
    beta_split_disconnected_of_old_cut M hx hy U hU hboundary⟩

/-- The source caps complete a chosen incoming/outgoing pair at a
four-valent atom to the actual remaining incoming/outgoing pair. -/
theorem exists_remaining_mixed_pair (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} {x y : D} (hv : v ∈ M.atoms) (hv4 : M.deg v = 4)
    (hx : M.atom x = v) (hy : M.atom y = v)
    (hxo : M.out x = false) (hyo : M.out y = true) :
    ∃ r s : D, M.atom r = v ∧ M.atom s = v ∧ M.out r = false ∧ M.out s = true ∧
      x ≠ y ∧ x ≠ r ∧ x ≠ s ∧ y ≠ r ∧ y ≠ s ∧ r ≠ s ∧
      M.dartsAt v = {x,y,r,s} := by
  classical
  have hc := hM.1 v hv
  have hsum := Mole.outdeg_add_indeg M v
  have hi : ((M.dartsAt v).filter (fun z => M.out z = false)).card = 2 := by
    change M.indeg v = 2
    omega
  have ho : ((M.dartsAt v).filter (fun z => M.out z = true)).card = 2 := by
    change M.outdeg v = 2
    omega
  have hxin : x ∈ (M.dartsAt v).filter (fun z => M.out z = false) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M v x).mpr hx,hxo⟩
  have hyout : y ∈ (M.dartsAt v).filter (fun z => M.out z = true) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M v y).mpr hy,hyo⟩
  have hri : (((M.dartsAt v).filter (fun z => M.out z = false)).erase x).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hxin,hi]
    decide
  have hso : (((M.dartsAt v).filter (fun z => M.out z = true)).erase y).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hyout,ho]
    decide
  obtain ⟨r,hr⟩ := hri
  obtain ⟨s,hs⟩ := hso
  obtain ⟨hrx,hr⟩ := mem_erase.mp hr
  obtain ⟨hsy,hs⟩ := mem_erase.mp hs
  obtain ⟨hrv,hro⟩ := mem_filter.mp hr
  obtain ⟨hsv,hso⟩ := mem_filter.mp hs
  have hrv' := (Mole.mem_dartsAt M v r).mp hrv
  have hsv' := (Mole.mem_dartsAt M v s).mp hsv
  have hxy : x ≠ y := by intro h; simpa [hxo,hyo] using congrArg M.out h
  have hxs : x ≠ s := by intro h; simpa [hxo,hso] using congrArg M.out h
  have hyr : y ≠ r := by intro h; simpa [hyo,hro] using congrArg M.out h
  have hrs : r ≠ s := by intro h; simpa [hro,hso] using congrArg M.out h
  have hxr : x ≠ r := Ne.symm hrx
  have hys : y ≠ s := Ne.symm hsy
  refine ⟨r,s,hrv',hsv',hro,hso,hxy,hxr,hxs,hyr,hys,hrs,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M v x).mpr hx,(Mole.mem_dartsAt M v y).mpr hy,hrv,hsv⟩
  · change M.deg v ≤ _
    simp only [hv4]
    simp [hxy,hxr,hxs,hyr,hys,hrs]

/-- A mixed two-bond boundary whose two darts both lie at the joint also
forces beta: use the complementary OLD atom set. This is the repeated
shared-label branch in source good case (1). -/
theorem admitsBetaSplit_of_mixed_boundary_at_joint (M : Molecule V D) {v : V} {x y : D}
    (hv4 : M.deg v = 4) (hx : M.atom x = v) (hy : M.atom y = v)
    (hxo : M.out x = false) (hyo : M.out y = true)
    (hbridge : ∀ e, M.atom e = v → ¬ IsBridge M e)
    (S : Finset V) (hboundary : boundaryDarts M S = {x,y}) : AdmitsBetaSplit M := by
  classical
  have hxS : x ∈ boundaryDarts M S := by rw [hboundary]; simp
  have hvS : v ∈ S := hx ▸ (mem_filter.mp hxS).2.1
  have hU : M.atoms \ S ⊆ M.atoms \ {v} := by
    intro a ha
    have hh := mem_sdiff.mp ha
    exact mem_sdiff.mpr ⟨hh.1,by
      simp only [mem_singleton]
      exact fun h => hh.2 (h.symm ▸ hvS)⟩
  have hb : boundaryDarts M (M.atoms \ S) = {M.mate x,M.mate y} := by
    rw [boundary_atoms_sdiff_eq_image_mate M S,hboundary,image_insert,image_singleton]
  exact admitsBetaSplit_of_old_mixed_cut M (hx ▸ M.atom_mem x) hv4 hx hy hxo hyo hbridge
    (M.atoms \ S) hU hb

/-- Absence of beta forces a two-bond boundary concentrated at a
four-valent joint to have the same direction. -/
theorem out_eq_of_joint_two_boundary_no_beta (M : Molecule V D) {v : V} {x y : D}
    (hv4 : M.deg v = 4) (hx : M.atom x = v) (hy : M.atom y = v)
    (hbridge : ∀ e, M.atom e = v → ¬ IsBridge M e)
    (hno : ¬ AdmitsBetaSplit M) (S : Finset V) (hboundary : boundaryDarts M S = {x,y}) :
    M.out x = M.out y := by
  cases hxo : M.out x <;> cases hyo : M.out y
  · rfl
  · exact False.elim (hno (admitsBetaSplit_of_mixed_boundary_at_joint M hv4 hx hy hxo hyo hbridge S hboundary))
  · have hb : boundaryDarts M S = {y,x} := by rw [hboundary,pair_comm]
    exact False.elim (hno (admitsBetaSplit_of_mixed_boundary_at_joint M hv4 hy hx hyo hxo hbridge S hb))
  · rfl

end WaveTurbulence.MoleProp

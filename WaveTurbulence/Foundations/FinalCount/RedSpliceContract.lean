/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockContraction
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), molecule level: a block disjoint from a contracted group stays a block

`contractGroup M S` merges the atoms of `S` into one atom (`none`) and deletes the darts internal to `S`.
A block `U` disjoint from `S` keeps all its darts, so its image in the contraction is a block with the
images of its joints.  This is the non-touching transport used to iterate single-block splices.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S U : Finset V}

/-- The image of an atom set in the contraction. -/
@[expose] def cvImage (S U : Finset V) : Finset (ContractVertex S) := U.image (contractVertex S)

theorem contractVertex_of_notMem {v : V} (h : v ∉ S) : contractVertex S v = some ⟨v, h⟩ := by
  simp [contractVertex, h]

theorem contractVertex_inj_of_disjoint (hd : Disjoint U S) {u v : V} (hu : u ∈ U) (hv : v ∈ U ∨ v ∉ S)
    (h : contractVertex S u = contractVertex S v) : u = v := by
  have hu' : u ∉ S := fun hs => Finset.disjoint_left.mp hd hu hs
  rcases hv with hv | hv
  · have hv' : v ∉ S := fun hs => Finset.disjoint_left.mp hd hv hs
    exact contractVertex_outside_injective hu' hv' h
  · exact contractVertex_outside_injective hu' hv h

theorem mem_cvImage (hd : Disjoint U S) {v : V} :
    contractVertex S v ∈ cvImage S U ↔ v ∈ U := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    by_cases hv : v ∈ S
    · exfalso
      have : contractVertex S u = none := by rw [he]; exact (contractVertex_eq_none S v).mpr hv
      exact Finset.disjoint_left.mp hd hu ((contractVertex_eq_none S u).mp this)
    · have := contractVertex_inj_of_disjoint hd hu (Or.inr hv) he
      exact this ▸ hu
  · intro h
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

theorem inGroup_cvImage (hd : Disjoint U S) (x : ContractDart M S) :
    (contractGroup M S).InGroup (cvImage S U) x ↔ M.InGroup U x.1 := by
  change contractVertex S (M.atom x.1) ∈ _ ∧ contractVertex S (M.atom (M.mate x.1)) ∈ _ ↔ _
  rw [mem_cvImage hd, mem_cvImage hd]
  rfl


theorem not_inGroup_of_atom_mem (hd : Disjoint U S) {x : D} (hx : M.atom x ∈ U) : ¬ M.InGroup S x :=
  fun h => Finset.disjoint_left.mp hd hx h.1

/-- The darts at a surviving atom of `U` that lie in `U` (with a property `P`) correspond bijectively. -/
theorem card_filter_contract (hd : Disjoint U S) (P : D → Prop) [DecidablePred P] {v : V} (hv : v ∈ U) :
    (((contractGroup M S).dartsAt (contractVertex S v)).filter
        (fun x' => (contractGroup M S).InGroup (cvImage S U) x' ∧ P x'.1)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup U x ∧ P x)).card := by
  have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hd hv h
  apply Finset.card_bij (fun x' _ => x'.1)
  · intro x' hx'
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hx' ⊢
    obtain ⟨h1, h2, h3⟩ := hx'
    refine ⟨?_, (inGroup_cvImage hd x').mp h2, h3⟩
    have hnone : contractVertex S (M.atom x'.1) ≠ none := by
      change (contractGroup M S).atom x' ≠ none
      rw [h1, Ne, contractVertex_eq_none]; exact hvS
    exact contractVertex_outside_injective (fun hs => hnone ((contractVertex_eq_none S _).mpr hs)) hvS h1
  · intro x y _ _ h
    exact Subtype.ext h
  · intro x hx
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have hnot : ¬ M.InGroup S x := not_inGroup_of_atom_mem hd (h1 ▸ hv)
    refine ⟨⟨x, hnot⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and]
    refine ⟨?_, (inGroup_cvImage hd ⟨x, hnot⟩).mpr h2, h3⟩
    change contractVertex S (M.atom x) = _
    rw [h1]

theorem isBlock_contract (hd : Disjoint U S) {a b : V} (hB : M.IsBlock U a b) :
    (contractGroup M S).IsBlock (cvImage S U) (contractVertex S a) (contractVertex S b) := by
  obtain ⟨hsub, ha, hb, hab, h1, h2, h3, h4, h5, h6⟩ := hB
  have haS : a ∉ S := fun h => Finset.disjoint_left.mp hd ha h
  have hbS : b ∉ S := fun h => Finset.disjoint_left.mp hd hb h
  refine ⟨?_, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨u, hsub hu, rfl⟩
  · intro h
    exact hab (contractVertex_outside_injective haS hbS h)
  · have := card_filter_contract (M := M) hd (fun x => M.out x = true) ha
    exact this.trans h1
  · have := card_filter_contract (M := M) hd (fun x => M.out x = false) ha
    exact this.trans h2
  · have := card_filter_contract (M := M) hd (fun x => M.out x = true) hb
    exact this.trans h3
  · have := card_filter_contract (M := M) hd (fun x => M.out x = false) hb
    exact this.trans h4
  · intro v hv hva hvb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have huS : u ∉ S := fun h => Finset.disjoint_left.mp hd hu h
    have hua : u ≠ a := fun h => hva (h ▸ rfl)
    have hub : u ≠ b := fun h => hvb (h ▸ rfl)
    have := card_filter_contract (M := M) hd (fun _ => True) hu
    simp only [and_true] at this
    exact this.trans (h5 u hu hua hub)
  · intro u' hu' v' hv'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hv'
    have hp := h6 u hu v hv
    clear hu hv hu' hv'
    induction hp with
    | rel a b hab =>
      obtain ⟨x, hx, hxa, hxb⟩ := hab
      apply Relation.EqvGen.rel
      refine ⟨⟨x, not_inGroup_of_atom_mem hd hx.1⟩, (inGroup_cvImage hd _).mpr hx, ?_, ?_⟩
      · change contractVertex S (M.atom x) = _
        rw [hxa]
      · change contractVertex S (M.atom (M.mate x)) = _
        rw [hxb]
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.RedSplice

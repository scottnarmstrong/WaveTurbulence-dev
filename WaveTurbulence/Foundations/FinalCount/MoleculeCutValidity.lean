/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeCutParameters
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-!
# Actual half-edge cuts preserve the molecule axioms

TARGET `defcut`: orientation bounds follow from the degree split. A new
saturated component cannot occur: it would avoid both degree-at-most-two
cut atoms and would already be a saturated component of the old molecule.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  (M : Molecule V D) {v v2 : V} {x1 x2 : D}

omit [Fintype D] in
/-- A cut either keeps an incidence at its old atom or moves it from v to v2. -/
theorem cut_atom_cases (x : D) :
    (M.cut v v2 x1 x2).atom x = M.atom x ∨
      (M.atom x = v ∧ (M.cut v v2 x1 x2).atom x = v2) := by
  by_cases hx : M.atom x = v ∧ x ≠ x1 ∧ x ≠ x2
  · exact Or.inr ⟨hx.1,by simp [Molecule.cut,hx.1,hx.2.1,hx.2.2]⟩
  · exact Or.inl (by simp only [Molecule.cut,hx,ite_false])

/-- Both cut atoms have degree at most two. -/
theorem cut_small_degrees (hM : M.IsMolecule) (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).deg v ≤ 2 ∧ (M.cut v v2 x1 x2).deg v2 ≤ 2 := by
  have h1 := cut_deg_old M hd
  have h2 := cut_deg_new_add_two M hd
  have ho := deg_le_four M hM hd.1
  omega

/-- A genuine cut of a molecule is again a molecule, including the
no-saturated-component axiom and all self-loop cases. -/
theorem cut_isMolecule (hM : M.IsMolecule) (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).IsMolecule := by
  let C := M.cut v v2 x1 x2
  have hsmall := cut_small_degrees M hM hd
  change C.deg v ≤ 2 ∧ C.deg v2 ≤ 2 at hsmall
  have hbounds : ∀ z ∈ C.atoms, C.outdeg z ≤ 2 ∧ C.indeg z ≤ 2 := by
    intro z hz
    by_cases h1 : z = v
    · subst z
      have hs := outdeg_add_indeg C v
      omega
    · by_cases h2 : z = v2
      · subst z
        have hs := outdeg_add_indeg C v2
        omega
      · have hzold : z ∈ M.atoms := (Finset.mem_insert.mp hz).resolve_left h2
        have ho : C.outdeg z = M.outdeg z := by
          change (M.cut v v2 x1 x2).outdeg z = M.outdeg z
          unfold Molecule.outdeg
          rw [cut_dartsAt_other M h1 h2]
          rfl
        have hi : C.indeg z = M.indeg z := by
          change (M.cut v v2 x1 x2).indeg z = M.indeg z
          unfold Molecule.indeg
          rw [cut_dartsAt_other M h1 h2]
          rfl
        rw [ho,hi]
        exact hM.1 z hzold
  refine ⟨hbounds,?_⟩
  intro z hz
  by_contra hn
  have hall (u : V) (hu : u ∈ C.atoms) (hp : C.SameComponent z u) : C.deg u = 4 := by
    by_contra h4
    exact hn ⟨u,hu,hp,h4⟩
  let P : V → Prop := fun u => C.SameComponent z u
  have hfour (u : V) (hp : P u) : C.deg u = 4 :=
    hall u ((sameComponent_mem_iff C hp).mp hz) hp
  have havoid (u : V) (hp : P u) : u ≠ v ∧ u ≠ v2 := by
    have h4 := hfour u hp
    constructor <;> intro he <;> subst u <;> omega
  have hstep : ∀ {w t : V}, P w → M.Adj w t → P t := by
    intro w t hw ht
    obtain ⟨x,hxw,hxt⟩ := ht
    have hwa := havoid w hw
    have hcx : C.atom x = w := by
      rcases cut_atom_cases (v := v) (v2 := v2) (x1 := x1) (x2 := x2) M x with he | ⟨ho,he⟩
      · exact he.trans hxw
      · exact (hwa.1 (hxw.symm.trans ho)).elim
    have hpEnd : P (C.atom (M.mate x)) :=
      sameComponent_trans C hw (Relation.EqvGen.rel _ _ ⟨x,hcx,rfl⟩)
    have hEnd4 := hfour _ hpEnd
    have htv : t ≠ v := by
      intro he
      rcases cut_atom_cases (v := v) (v2 := v2) (x1 := x1) (x2 := x2) M (M.mate x) with hsame | ⟨hold,hmoved⟩
      · have hEq : C.atom (M.mate x) = v := hsame.trans (hxt.trans he)
        rw [hEq] at hEnd4
        omega
      · change C.atom (M.mate x) = v2 at hmoved
        rw [hmoved] at hEnd4
        omega
    have hEnd : C.atom (M.mate x) = t := by
      rcases cut_atom_cases (v := v) (v2 := v2) (x1 := x1) (x2 := x2) M (M.mate x) with hsame | ⟨hold,hmoved⟩
      · exact hsame.trans hxt
      · exact (htv (hxt.symm.trans hold)).elim
    exact hEnd ▸ hpEnd
  have hpath : ∀ {w t : V}, M.SameComponent w t → (P w ↔ P t) := by
    intro w t hp
    induction hp with
    | rel a b hab => exact ⟨fun ha => hstep ha hab,fun hb => hstep hb (adj_symmetric M hab)⟩
    | refl => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  have hzP : P z := sameComponent_refl C z
  have hzAvoid := havoid z hzP
  have hzold : z ∈ M.atoms := (Finset.mem_insert.mp hz).resolve_left hzAvoid.2
  obtain ⟨u,hu,hzu,hne4⟩ := hM.2 z hzold
  have huP := (hpath hzu).mp hzP
  have huAvoid := havoid u huP
  have hdu : C.deg u = M.deg u := by
    change (M.cut v v2 x1 x2).deg u = M.deg u
    unfold Molecule.deg
    rw [cut_dartsAt_other M huAvoid.1 huAvoid.2]
  have hu4 := hfour u huP
  rw [hdu] at hu4
  exact hne4 hu4

end WaveTurbulence.Mole

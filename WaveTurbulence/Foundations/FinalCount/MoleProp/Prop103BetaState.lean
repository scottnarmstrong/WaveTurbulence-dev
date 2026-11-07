/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.AtomEmbedding
import Mathlib.Tactic

/-! # A literal fresh-name formulation of the source beta operation -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source never needs an unused name in the old finite vertex type. -/
def someAtomEmbedding (V : Type*) : V ↪ Option V := ⟨some,Option.some_injective _⟩

/-- Old atoms embedded into a carrier with one guaranteed fresh name. -/
def withFreshAtom (M : Molecule V D) : Molecule (Option V) D :=
  mapAtoms M (someAtomEmbedding V)

/-- Literal source beta data: split a degree-four atom into balanced pairs,
with no incident bridge, and the two resulting joints disconnect. This
predicate asserts only an actual graph operation, never a counting estimate. -/
def AdmitsBetaSplit (M : Molecule V D) : Prop :=
  ∃ (v : V) (x y : D),
    (withFreshAtom M).IsCutData (some v) none x y ∧ M.deg v = 4 ∧
    (∀ e, M.atom e = v → ¬ IsBridge M e) ∧
    ¬ ((withFreshAtom M).cut (some v) none x y).SameComponent (some v) none

/-- Choosing opposite-direction darts from distinct bonds at an old atom
gives actual cut data with the guaranteed fresh name. -/
theorem isCutData_withFreshAtom (M : Molecule V D) {v : V} {x y : D}
    (hv : v ∈ M.atoms) (hx : M.atom x = v) (hy : M.atom y = v)
    (hxy : y ≠ M.mate x) (hxo : M.out x = false) (hyo : M.out y = true) :
    (withFreshAtom M).IsCutData (some v) none x y := by
  refine ⟨mem_map.mpr ⟨v,hv,rfl⟩,?_,congrArg some hx,congrArg some hy,hxy,hxo,hyo⟩
  intro h
  obtain ⟨a,_,ha⟩ := mem_map.mp h
  change (some a : Option V) = none at ha
  cases ha

/-- Both actual beta joints have degree two. -/
theorem beta_joint_degrees (M : Molecule V D) {v : V} {x y : D}
    (hd : (withFreshAtom M).IsCutData (some v) none x y) (hv4 : M.deg v = 4) :
    ((withFreshAtom M).cut (some v) none x y).deg (some v) = 2 ∧
      ((withFreshAtom M).cut (some v) none x y).deg none = 2 := by
  have h1 := Mole.cut_deg_old (withFreshAtom M) hd
  have h2 := Mole.cut_deg_new_add_two (withFreshAtom M) hd
  have hdeg : (withFreshAtom M).deg (some v) = M.deg v := by
    exact congrArg Finset.card (mapAtoms_dartsAt M (someAtomEmbedding V) v)
  exact ⟨h1,by omega⟩

/-- Injectively renaming atom names preserves actual bridges. -/
theorem mapAtoms_isBridge_iff {W : Type*} [DecidableEq W]
    (M : Molecule V D) (f : V ↪ W) (e : D) : IsBridge (mapAtoms M f) e ↔ IsBridge M e := by
  classical
  letI : Nonempty V := ⟨M.atom e⟩
  let g : W → V := Function.invFun f
  have hg (a : V) : g (f a) = a := Function.leftInverse_invFun f.injective a
  have hforward (a b : V) (hab : AdjWithoutBond M e a b) :
      AdjWithoutBond (mapAtoms M f) e (f a) (f b) := by
    obtain ⟨x,hxa,hxb,hxe,hxme⟩ := hab
    exact ⟨x,congrArg f hxa,congrArg f hxb,hxe,hxme⟩
  have hback (a b : W) (hab : AdjWithoutBond (mapAtoms M f) e a b) :
      AdjWithoutBond M e (g a) (g b) := by
    obtain ⟨x,hxa,hxb,hxe,hxme⟩ := hab
    refine ⟨x,?_,?_,hxe,hxme⟩
    · rw [← hxa]
      exact (hg (M.atom x)).symm
    · rw [← hxb]
      exact (hg (M.atom (M.mate x))).symm
  have hpforward (a b : V) (hp : Relation.EqvGen (AdjWithoutBond M e) a b) :
      Relation.EqvGen (AdjWithoutBond (mapAtoms M f) e) (f a) (f b) := by
    induction hp with
    | rel a b h => exact Relation.EqvGen.rel _ _ (hforward a b h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  constructor
  · intro hb hp
    exact hb (hpforward _ _ hp)
  · intro hb hp
    have hproj (a b : W) (hp : Relation.EqvGen (AdjWithoutBond (mapAtoms M f) e) a b) :
        Relation.EqvGen (AdjWithoutBond M e) (g a) (g b) := by
      induction hp with
      | rel a b h => exact Relation.EqvGen.rel _ _ (hback a b h)
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    apply hb
    have hh := hproj _ _ hp
    change Relation.EqvGen (AdjWithoutBond M e) (g (f (M.atom e)))
      (g (f (M.atom (M.mate e)))) at hh
    simpa only [hg] using hh

end WaveTurbulence.MoleProp

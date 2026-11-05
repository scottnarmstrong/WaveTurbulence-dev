/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIICardinality
public import WaveTurbulence.Foundations.Molecule.VineSideVIIBranches
public import WaveTurbulence.Foundations.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.Molecule.VineShortGraphConnectivity
public import WaveTurbulence.Foundations.Molecule.VineSelectedBonds
public import WaveTurbulence.Foundations.Molecule.VineSideRestriction
import Mathlib.Tactic

/-! # A nontrivial VC in the type-VII side has at least two full rungs -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A VC larger than a double bond avoiding the outer joints in type VII
is the full side with kc>=2. The five/seven-atom short sides are excluded
using explicit paths after deletion of any atom. The seven-atom
concatenation of two Q-blocks is thereby distinguished (F72). -/
theorem typeVII_VC_side_length (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hVC : IsVC M A x y) (hAS : A ⊆ S)
    (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) :
    ∃ kr kc kg,R.k=[kr,kc,kg] ∧ 2 ≤ kc ∧ A=R.selectedAtoms (sideLabels (11+2*kr) kc) ∧
      A.card=5+2*kc ∧ ({x,y} : Finset V)={(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} := by
  obtain ⟨kr,kc,kg,hks,hAe,hcount,hj⟩ := typeVII_inner_side_card M hM R hS hVC.1
    (isVC_connected hVC) hAS hcard ha hb
  have hk : 2 ≤ kc := by
    by_contra hh
    have hshort : kc=0 ∨ kc=1 := by omega
    have hc : A.card=5 ∨ A.card=7 := by omega
    let N := 11+2*kr
    let W := sideLabels N kc
    have hW : W ⊆ range (VineType.VII.expand R.k).n := by
      intro i hi
      have hp := (mem_sideLabels_iff N kc i).mp hi
      rw [hks,expand_atoms_exact .VII [kr,kc,kg] rfl]
      simp only [VineType.template,List.sum_cons,List.sum_nil,Nat.add_zero]
      apply mem_range.mpr
      dsimp [N] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | ⟨_hlo,hhi⟩ <;> omega
    have himage : A.image R.f=W := by
      rw [hAe,R.image_selectedAtoms,inter_eq_left.mpr hW]
    have hbonds : (M.groupBonds A).map (Sym2.map R.f)=rawBondMultiset (sideBonds N kc) := by
      have hb := R.selected_bonds W hW
      rw [hks,typeVII_side_restrict_bonds] at hb
      simpa only [hAe,W,N] using hb
    have hinj : Set.InjOn R.f A := fun _ hu _ hv he => R.injOn (hAS hu) (hAS hv) he
    have hconn := erase_connected_of_label_paths x hVC.1.2.1 R.f hinj W himage
      (sideBonds N kc) (short_side_endpoints N kc hshort)
      (fun u hu v hv hedge => adj_of_label_bonds R.f hinj _ hbonds hu hv hedge)
      (isVC_connected hVC) (fun z hz u hu v hv huz hvz =>
        short_side_paths N kc (by dsimp [N]; omega) hshort z u v hz hu hv huz hvz)
    exact not_isVC_five_or_seven_of_erase_connected M hM hc hconn hVC
  exact ⟨kr,kc,kg,hks,hk,hAe,hcount,hj⟩

end WaveTurbulence.Vine

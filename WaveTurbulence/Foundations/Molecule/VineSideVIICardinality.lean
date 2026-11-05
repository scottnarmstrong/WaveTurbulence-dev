/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFullSideVII
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineSelectedAtoms
import Mathlib.Tactic

/-! # Exact atom set and size of a full type-VII side block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual type-VII side block has the selected label set and exactly
5+2kc atoms. Both facts follow from the proved containment and closure,
not from a presumed side-block or cardinality hypothesis. -/
theorem typeVII_inner_side_card (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) :
    ∃ kr kc kg,R.k=[kr,kc,kg] ∧ A=R.selectedAtoms (sideLabels (11+2*kr) kc) ∧
      A.card=5+2*kc ∧ ({x,y} : Finset V)={(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} := by
  obtain ⟨kr,kc,kg,hks,hfull,hj⟩ := typeVII_inner_full_side M hM R hS hA hC hAS hcard ha hb
  let W := sideLabels (11+2*kr) kc
  have hW : W ⊆ range (VineType.VII.expand R.k).n := by
    intro i hi
    have hp := (mem_sideLabels_iff (11+2*kr) kc i).mp hi
    apply mem_range.mpr
    rw [hks,expand_atoms]
    norm_num [VineType.template]
    rcases hp with rfl | rfl | rfl | rfl | rfl | ⟨_hlo,hhi⟩ <;> omega
  have hAe : A=R.selectedAtoms W := by
    ext v
    constructor
    · intro hv
      exact mem_filter.mpr ⟨hAS hv,(mem_sideLabels_iff _ _ _).mpr ((hfull v (hAS hv)).mp hv)⟩
    · intro hv
      have hh := mem_filter.mp hv
      exact (hfull v hh.1).mpr ((mem_sideLabels_iff _ _ _).mp hh.2)
  have hcA : A.card=5+2*kc := by
    rw [hAe,R.card_selectedAtoms W hW]
    exact sideLabels_card _ _ (by omega)
  exact ⟨kr,kc,kg,hks,hAe,hcA,hj⟩

end WaveTurbulence.Vine

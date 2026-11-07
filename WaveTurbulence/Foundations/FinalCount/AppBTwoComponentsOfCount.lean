/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSidePaths
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
import Mathlib.Tactic

/-! # Recover the actual two connected pieces from their quotient count -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_twoComponents_of_count (M : Molecule V D) (hF : M.numComponents = 2)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : ¬M.SameComponent a b) :
    TwoComponents M M.atoms a b := by
  classical
  let U := Degen.componentSet M a
  let W := Degen.componentSet M b
  have hcover : U ∪ W = M.atoms := by
    ext v
    constructor
    · intro h
      rcases mem_union.mp h with h | h
      · exact ((Degen.mem_componentSet M a v).mp h).1
      · exact ((Degen.mem_componentSet M b v).mp h).1
    · intro hv
      by_cases hav : M.SameComponent a v
      · exact mem_union_left _ ((Degen.mem_componentSet M a v).mpr ⟨hv,hav⟩)
      · exact mem_union_right _ ((Degen.mem_componentSet M b v).mpr
          ⟨hv,appb_sameComponent_of_two_of_not M hF ha hb hv hab hav⟩)
  have hdis : Disjoint U W := by
    apply disjoint_left.mpr
    intro v hu hw
    exact hab (Relation.EqvGen.trans _ _ _ ((Degen.mem_componentSet M a v).mp hu).2
      ((Degen.mem_componentSet M b v).mp hw).2.symm)
  refine ⟨U,W,hcover,hdis,appb_componentSet_groupConnected M ha,appb_componentSet_groupConnected M hb,
    (Degen.mem_componentSet M a a).mpr ⟨ha,Relation.EqvGen.refl _⟩,
    (Degen.mem_componentSet M b b).mpr ⟨hb,Relation.EqvGen.refl _⟩,?_⟩
  intro u hu v hv hadj
  have hp : M.SameComponent u v := Relation.EqvGen.rel _ _ hadj
  exact hab (Relation.EqvGen.trans _ _ _ ((Degen.mem_componentSet M a u).mp hu).2
    (Relation.EqvGen.trans _ _ _ hp ((Degen.mem_componentSet M b v).mp hv).2.symm))

end WaveTurbulence.Mole

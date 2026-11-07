/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Disjoint physical bond enumeration for two successive atom deletions -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbUnionBondEquiv (M : Molecule V D) (Y Z : Finset V) :
    ({x // x ∈ appbRemovedBonds M Y} ⊕
      {x // x ∈ appbRemovedBonds (Degen.eraseAtoms M Y) Z}) ≃
      {x // x ∈ appbRemovedBonds M (Y ∪ Z)} := by
  classical
  let f : ({x // x ∈ appbRemovedBonds M Y} ⊕
      {x // x ∈ appbRemovedBonds (Degen.eraseAtoms M Y) Z}) →
      {x // x ∈ appbRemovedBonds M (Y ∪ Z)} := fun x => match x with
    | .inl x => ⟨x.val,mem_filter.mpr ⟨(mem_filter.mp x.property).1,
        ((mem_filter.mp x.property).2).imp (mem_union_left Z) (mem_union_left Z)⟩⟩
    | .inr x => ⟨x.val.val,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
        (mem_filter.mp (mem_filter.mp x.property).1).2⟩,
        ((mem_filter.mp x.property).2).imp (mem_union_right Y) (mem_union_right Y)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (x|x) (y|y) he
      · have hv : x.val = y.val := congrArg (fun z : {x // x ∈ appbRemovedBonds M (Y ∪ Z)} => z.val) he
        exact congrArg Sum.inl (Subtype.ext hv)
      · have hv : x.val = y.val.val := congrArg Subtype.val he
        have ht := (mem_filter.mp x.property).2
        rw [hv] at ht
        exact False.elim (ht.elim y.val.property.1 y.val.property.2)
      · have hv : x.val.val = y.val := congrArg Subtype.val he
        have ht := (mem_filter.mp y.property).2
        rw [← hv] at ht
        exact False.elim (ht.elim x.val.property.1 x.val.property.2)
      · have hv : x.val.val = y.val.val := congrArg (fun z : {x // x ∈ appbRemovedBonds M (Y ∪ Z)} => z.val) he
        exact congrArg Sum.inr (Subtype.ext (Subtype.ext hv))
    · intro x
      by_cases hx : x.val ∈ appbRemovedBonds M Y
      · exact ⟨.inl ⟨x.val,hx⟩,rfl⟩
      · have hb := (mem_filter.mp x.property).1
        have hn : M.atom x.val ∉ Y ∧ M.atom (M.mate x.val) ∉ Y := by
          constructor
          · intro h
            exact hx (mem_filter.mpr ⟨hb,Or.inl h⟩)
          · intro h
            exact hx (mem_filter.mpr ⟨hb,Or.inr h⟩)
        have hz : M.atom x.val ∈ Z ∨ M.atom (M.mate x.val) ∈ Z := by
          have ht := (mem_filter.mp x.property).2
          simpa only [mem_union,hn.1,hn.2,false_or] using ht
        let xr : Degen.RetainedDart M Y := ⟨x.val,hn⟩
        have hr : xr ∈ appbRemovedBonds (Degen.eraseAtoms M Y) Z :=
          mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2⟩,hz⟩
        exact ⟨.inr ⟨xr,hr⟩,rfl⟩
  exact Equiv.ofBijective f hf

namespace AppbRealization
variable {M : Molecule V D} {P Q : AppbPattern}

noncomputable def combinedEdgeEnumeration (r : AppbRealization M P) (s : AppbRealization r.post Q) :
    Fin (P.edges.length+Q.edges.length) ≃ {x // x ∈ appbRemovedBonds M (r.removedAtoms ∪ s.removedAtoms)} :=
  (finSumFinEquiv.symm.trans (r.edge.sumCongr s.edge)).trans (appbUnionBondEquiv M r.removedAtoms s.removedAtoms)

end AppbRealization
end WaveTurbulence.Mole

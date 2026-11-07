/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkNeighbors
import Mathlib.Tactic

/-! # A selected link can be presented from any of its four atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem AppbLink.presentation_at {M : Molecule V D} {S : Finset V}
    (hS : AppbLink M S) {a : V} (ha : a ∈ S) :
    ∃ u v : Fin 2 → V,Degen.SourceLadder (m := 1) M u v ∧
      Molecule.ladderAtoms u v = S ∧ u 0 = a := by
  obtain ⟨u,v,hL,rfl⟩ := hS
  have hrev (p q : Fin 2 → V) :
      Molecule.ladderAtoms (fun j => p j.rev) (fun j => q j.rev) = Molecule.ladderAtoms p q := by
    ext x
    simp only [Molecule.ladderAtoms,mem_union,mem_image,mem_univ,true_and]
    constructor
    · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
      · exact Or.inl ⟨j.rev,hj⟩
      · exact Or.inr ⟨j.rev,hj⟩
    · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
      · exact Or.inl ⟨j.rev,by simpa only [Fin.rev_rev] using hj⟩
      · exact Or.inr ⟨j.rev,by simpa only [Fin.rev_rev] using hj⟩
  have hswap : Molecule.ladderAtoms v u = Molecule.ladderAtoms u v := union_comm _ _
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨u,v,hL,rfl,rfl⟩
    · exact ⟨(fun j => u j.rev),(fun j => v j.rev),Degen.sourceLadder_reverse M hL,hrev u v,rfl⟩
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨v,u,Degen.sourceLadder_swap M hL,hswap,rfl⟩
    · exact ⟨(fun j => v j.rev),(fun j => u j.rev),
        Degen.sourceLadder_reverse M (Degen.sourceLadder_swap M hL),(hrev v u).trans hswap,rfl⟩

end WaveTurbulence.Mole

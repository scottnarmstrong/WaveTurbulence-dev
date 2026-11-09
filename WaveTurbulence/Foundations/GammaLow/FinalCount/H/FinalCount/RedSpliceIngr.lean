/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIngr
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceRev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Collection
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceIngr`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): the ingredients of a VC group

A block cannot also be a hyper-block (`vc_not_hyper`: the joint internal degrees are `2` against `3`), so every
ingredient of a VC group, in the sense of `IsIngredient`, is a member of the unique spine in one of the two joint
orders (`isIngredient_vc`).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole WaveTurbulence.Stage1

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- Every ingredient (in the sense of `IsIngredient`) of a VC group is a member of its spine. -/
theorem isIngredient_vc (hM : M.IsMolecule) {S T : Finset V} {a b : V} {L : List (Finset V × V × V)}
    (hB : M.IsBlock S a b) (hs : Spine M L S a b) (h : IsIngredient M S T) :
    ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L := by
  rcases h with ⟨a', b', n, x, y, hB', hI⟩ | ⟨a', b', e, n, x, y, hends, _, hBe, _⟩
  · have hj := Vine.block_joints_unique M hB hB'
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      obtain ⟨L', hL', hm⟩ := Spine.mem_of_ingredient hI
      rw [Spine.unique hM hL' hs hB] at hm
      exact ⟨x, y, Or.inl hm⟩
    · subst h1; subst h2
      rcases hs.ingredient_mem_or_reverse hM hB hI with hm | hm
      · exact ⟨y, x, Or.inl hm⟩
      · exact ⟨x, y, Or.inl hm⟩
  · exact (vc_not_hyper hB ⟨e, hends, hBe⟩).elim

end WaveTurbulence.GammaLow.FinalCount.H

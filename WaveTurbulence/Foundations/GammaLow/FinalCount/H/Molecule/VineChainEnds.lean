/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainEnds`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Small chains have double-bond end ingredients (TARGET subsetvc) -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
set_option linter.unusedSectionVars false

/-- The first ingredient retains the chain's first joint. -/
theorem chain_first_ingredient {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) :
    ∃ A x, Src.IsSomeVine Src.γL M A a x ∧ A ⊆ S := by
  induction h with
  | single h => exact ⟨_,_,h,subset_refl _⟩
  | append _ _ _ _ ih =>
    obtain ⟨A,x,hX,hA⟩ := ih
    exact ⟨A,x,hX,hA.trans subset_union_left⟩

/-- Unless it is a single ingredient, a chain on fewer than seven atoms
has a type-I ingredient at one of its two ends. -/
theorem chain_small_end_typeI {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) (hc : S.card<7) : n=1 ∨
      (∃ A x, M.IsVine .I A a x ∧ A ⊆ S) ∨
      (∃ A x, M.IsVine .I A x b ∧ A ⊆ S) := by
  cases h with
  | single => exact Or.inl rfl
  | @append S T a m c n hS hT hi _hne =>
    obtain ⟨A,x,hX,hA⟩ := chain_first_ingredient hS
    by_cases hXI : M.IsVine .I A a x
    · exact Or.inr (Or.inl ⟨A,x,hXI,hA.trans subset_union_left⟩)
    · by_cases hYI : M.IsVine .I T m b
      · exact Or.inr (Or.inr ⟨T,m,hYI,subset_union_right⟩)
      · have hAc : 4 ≤ A.card := by
          by_contra hh
          exact hXI (isSomeVine_typeI_of_card_lt_four hX (by omega))
        have hTc : 4 ≤ T.card := by
          by_contra hh
          exact hYI (isSomeVine_typeI_of_card_lt_four hT (by omega))
        have hinter : A ∩ T ⊆ ({m} : Finset V) := by
          intro v hv
          rw [← hi]
          exact mem_inter.mpr ⟨hA (mem_inter.mp hv).1,(mem_inter.mp hv).2⟩
        have hci := card_le_card hinter
        rw [card_singleton] at hci
        have hU : A ∪ T ⊆ S ∪ T := by
          intro v hv
          rcases mem_union.mp hv with hv | hv
          · exact mem_union_left T (hA hv)
          · exact mem_union_right S hv
        have hcu := card_le_card hU
        have hsum := card_union_add_card_inter A T
        omega

end WaveTurbulence.GammaLow.FinalCount.H

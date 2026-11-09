/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineOrdinarySplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineOrdinarySplit`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # A vine avoiding a chain split joint lies strictly on one side -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A genuine vine contained in a split chain and avoiding the shared
junction lies on one side and is disjoint from the other side. -/
theorem ordinary_vine_split_disjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {n : ℕ} (hS : Src.Chain Src.γL M S a b n)
    (hT : Src.IsSomeVine Src.γL M T b c) (hi : S ∩ T={b})
    (hU : M.IsBlock (S ∪ T) a c) (hA : Src.IsSomeVine Src.γL M A x y)
    (hAU : A ⊆ S ∪ T) (hb : b ∉ A) :
    (A ⊆ S ∧ Disjoint A T) ∨ (A ⊆ T ∧ Disjoint A S) := by
  rcases RS.vine_in_terminal_split M hM hT.block hU (chain_joints_mem hS).2 hA hAU with hAS | hAT
  · apply Or.inl
    refine ⟨hAS,disjoint_left.mpr ?_⟩
    intro v hvA hvT
    have hm : v ∈ S ∩ T := mem_inter.mpr ⟨hAS hvA,hvT⟩
    rw [hi] at hm
    exact hb (mem_singleton.mp hm ▸ hvA)
  · apply Or.inr
    refine ⟨hAT,disjoint_left.mpr ?_⟩
    intro v hvA hvS
    have hm : v ∈ S ∩ T := mem_inter.mpr ⟨hvS,hAT hvA⟩
    rw [hi] at hm
    exact hb (mem_singleton.mp hm ▸ hvA)

end WaveTurbulence.GammaLow.FinalCount.H

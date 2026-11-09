/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainInteriorConnected`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Removing the two outer joints leaves a connected chain interior -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Removing the first endpoint of a chain leaves every atom connected
to the surviving other endpoint. -/
theorem chain_erase_first_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : GroupConnected M (S.erase a) := by
  have reach (u : V) (hu : u ∈ S.erase a) : (Mole.induced M (S.erase a)).SameComponent b u := by
    rcases chain_erase_endpoint_reach (z := a) h u hu with ⟨hne,_hp⟩ | ⟨_hne,hp⟩
    · exact False.elim (hne rfl)
    · exact hp
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

/-- TARGET defvine/subsetvc: all nonjoint atoms of any source vine chain
form a connected region. This includes empty interiors and double-bond chains. -/
theorem chain_interior_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : GroupConnected M (S \ {a,b}) := by
  cases h with
  | single h =>
    have hX := h
    exact (Src.IsSomeVine.interior_connected hX)
  | @append S T a b c n hS hT hi _hne =>
    rename_i c
    have hX := hT
    have hs := chain_joints_mem hS
    have hab := chain_joints_ne hS
    have hbc := hX.block.2.2.2.1
    have hcS : c ∉ S := by
      intro hcS
      have he : c=b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS,hX.block.2.2.1⟩)
      exact hbc he.symm
    have haT : a ∉ T := by
      intro haT
      exact hab (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs.1,haT⟩))
    have liftS : S.erase a ⊆ (S ∪ T) \ {a,c} := by
      intro v hv
      obtain ⟨hva,hvS⟩ := mem_erase.mp hv
      refine mem_sdiff.mpr ⟨mem_union_left _ hvS,?_⟩
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨hva,fun he => hcS (he ▸ hvS)⟩
    have liftT : T.erase c ⊆ (S ∪ T) \ {a,c} := by
      intro v hv
      obtain ⟨hvc,hvT⟩ := mem_erase.mp hv
      refine mem_sdiff.mpr ⟨mem_union_right _ hvT,?_⟩
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨fun he => haT (he ▸ hvT),hvc⟩
    have reach (u : V) (hu : u ∈ (S ∪ T) \ {a,c}) :
        (Mole.induced M ((S ∪ T) \ {a,c})).SameComponent b u := by
      obtain ⟨huU,huj⟩ := mem_sdiff.mp hu
      have hune : u ≠ a ∧ u ≠ c := by simpa only [mem_insert,mem_singleton,not_or] using huj
      rcases mem_union.mp huU with huS | huT
      · exact induced_path_mono M liftS
          (chain_erase_first_connected hS b (mem_erase.mpr ⟨hab.symm,hs.2⟩) u (mem_erase.mpr ⟨hune.1,huS⟩))
      · exact induced_path_mono M liftT
          ((Src.IsSomeVine.erase_connected hX) c b (mem_erase.mpr ⟨hbc,hX.block.2.1⟩) u (mem_erase.mpr ⟨hune.2,huT⟩))
    intro u hu v hv
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

end WaveTurbulence.GammaLow.FinalCount.H

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainIngredients`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Ingredient certificates and geometric localization in an actual vine chain -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A particular vine ingredient in an actual ordered chain decomposition.
The constructors record only the defining source concatenations. -/
inductive ChainIngredient (M : Molecule V D) :
    Finset V → V → V → ℕ → Finset V → V → V → Prop
  | single {S a b} : Src.IsSomeVine Src.γL M S a b → ChainIngredient M S a b 1 S a b
  | append_left {S T A a b c x y n} : ChainIngredient M S a b n A x y →
      Src.IsSomeVine Src.γL M T b c → S ∩ T={b} → a ≠ c →
      ChainIngredient M (S ∪ T) a c (n+1) A x y
  | append_last {S T a b c n} : Src.Chain Src.γL M S a b n → Src.IsSomeVine Src.γL M T b c →
      S ∩ T={b} → a ≠ c → ChainIngredient M (S ∪ T) a c (n+1) T b c

/-- An ingredient certificate includes its genuine vine and containing chain. -/
theorem chainIngredient_spec {M : Molecule V D} {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredient M U a b n A x y) :
    Src.Chain Src.γL M U a b n ∧ Src.IsSomeVine Src.γL M A x y ∧ A ⊆ U := by
  induction h with
  | single h => exact ⟨Src.Chain.single h,h,subset_refl _⟩
  | append_left _ hT hi hne ih =>
    exact ⟨Src.Chain.append ih.1 hT hi hne,ih.2.1,ih.2.2.trans subset_union_left⟩
  | append_last hS hT hi hne => exact ⟨Src.Chain.append hS hT hi hne,hT,subset_union_right⟩

/-- Every actual atom of a chain belongs to one of its actual ingredients. -/
theorem chain_atom_ingredient {M : Molecule V D} {U : Finset V} {a b v : V} {n : ℕ}
    (h : Src.Chain Src.γL M U a b n) (hv : v ∈ U) :
    ∃ A x y,ChainIngredient M U a b n A x y ∧ v ∈ A := by
  induction h with
  | single h => exact ⟨_,_,_,ChainIngredient.single h,hv⟩
  | append hS hT hi hne ih =>
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨A,x,y,hA,hvA⟩ := ih hv
      exact ⟨A,x,y,ChainIngredient.append_left hA hT hi hne,hvA⟩
    · exact ⟨_,_,_,ChainIngredient.append_last hS hT hi hne,hv⟩

/-- Main's `vine_in_terminal_split` for a family member: a member inside a block split at the initial joint of a
terminal block lies on one side (it stays connected after deleting the split joint: `Src.IsSomeVine.erase_connected`). -/
theorem vine_in_terminal_splitS (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V}
    (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hbS : b ∈ S)
    (hA : Src.IsSomeVine Src.γL M A x y) (hAU : A ⊆ S ∪ T) : A ⊆ S ∨ A ⊆ T := by
  apply connected_erase_subset_side M S T A b hbS hT.2.1 hAU
    (fun v hv hvb u hu huv => terminal_block_adj_mem M hM hT hU subset_union_right hv hvb hu huv)
  exact Src.IsSomeVine.erase_connected hA b

end WaveTurbulence.GammaLow.FinalCount.H

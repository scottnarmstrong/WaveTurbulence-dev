/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineSeparatorLocalization
import Mathlib.Tactic

/-! # Ingredient certificates and geometric localization in an actual vine chain -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A particular vine ingredient in an actual ordered chain decomposition.
The constructors record only the defining source concatenations. -/
inductive ChainIngredient (M : Molecule V D) :
    Finset V → V → V → ℕ → Finset V → V → V → Prop
  | single {S a b} : IsSomeVine M S a b → ChainIngredient M S a b 1 S a b
  | append_left {S T A a b c x y n} : ChainIngredient M S a b n A x y →
      IsSomeVine M T b c → S ∩ T={b} → a ≠ c →
      ChainIngredient M (S ∪ T) a c (n+1) A x y
  | append_last {S T a b c n} : Chain M S a b n → IsSomeVine M T b c →
      S ∩ T={b} → a ≠ c → ChainIngredient M (S ∪ T) a c (n+1) T b c

/-- An ingredient certificate includes its genuine vine and containing chain. -/
theorem chainIngredient_spec {M : Molecule V D} {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredient M U a b n A x y) :
    Chain M U a b n ∧ IsSomeVine M A x y ∧ A ⊆ U := by
  induction h with
  | single h => exact ⟨Chain.single h,h,subset_refl _⟩
  | append_left _ hT hi hne ih =>
    exact ⟨Chain.append ih.1 hT hi hne,ih.2.1,ih.2.2.trans subset_union_left⟩
  | append_last hS hT hi hne => exact ⟨Chain.append hS hT hi hne,hT,subset_union_right⟩

/-- Every actual atom of a chain belongs to one of its actual ingredients. -/
theorem chain_atom_ingredient {M : Molecule V D} {U : Finset V} {a b v : V} {n : ℕ}
    (h : Chain M U a b n) (hv : v ∈ U) :
    ∃ A x y,ChainIngredient M U a b n A x y ∧ v ∈ A := by
  induction h with
  | single h => exact ⟨_,_,_,ChainIngredient.single h,hv⟩
  | append hS hT hi hne ih =>
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨A,x,y,hA,hvA⟩ := ih hv
      exact ⟨A,x,y,ChainIngredient.append_left hA hT hi hne,hvA⟩
    · exact ⟨_,_,_,ChainIngredient.append_last hS hT hi hne,hv⟩

end WaveTurbulence.Vine

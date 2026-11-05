/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # A vine avoiding a chain split joint lies strictly on one side -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A genuine vine contained in a split chain and avoiding the shared
junction lies on one side and is disjoint from the other side. -/
theorem ordinary_vine_split_disjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {n : ℕ} (hS : Chain M S a b n)
    {X : VineType} (hT : M.IsVine X T b c) (hi : S ∩ T={b})
    (hU : M.IsBlock (S ∪ T) a c) (hA : IsSomeVine M A x y)
    (hAU : A ⊆ S ∪ T) (hb : b ∉ A) :
    (A ⊆ S ∧ Disjoint A T) ∨ (A ⊆ T ∧ Disjoint A S) := by
  obtain ⟨Y,hY⟩ := hA
  rcases vine_in_terminal_split M hM hT.1 hU (chain_joints_mem hS).2 hY hAU with hAS | hAT
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

omit [Fintype D] in
/-- A global surviving atom in a local group survives all local pieces
when those pieces belong to the global family. -/
theorem remainingAtoms_local_of_global (U B : Finset V) (ps qs : List (RemovalPiece V D))
    (hqs : ∀ P ∈ qs,P ∈ ps) {v : V} (hv : v ∈ B) (hrem : v ∈ remainingAtoms U ps) :
    v ∈ remainingAtoms B qs := by
  refine mem_filter.mpr ⟨hv,?_⟩
  intro P hP
  exact (mem_filter.mp hrem).2 P (hqs P hP)

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
import Mathlib.Tactic

/-! # Every surviving chain atom reaches a surviving endpoint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Deleting a single atom from a chain leaves every remaining atom
connected to at least one surviving outer endpoint. Each vine ingredient's
vertex connectivity is proved from the literal templates. -/
theorem chain_erase_endpoint_reach {M : Molecule V D} {S : Finset V} {a b z : V} {n : ℕ}
    (h : Chain M S a b n) : ∀ u ∈ S.erase z,
      (a ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent a u) ∨
      (b ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent b u) := by
  induction h with
  | @single S a b h =>
    obtain ⟨X,hX⟩ := h
    intro u hu
    by_cases haz : a=z
    · have hbz : b ≠ z := by intro he; exact hX.1.2.2.2.1 (haz.trans he.symm)
      exact Or.inr ⟨hbz,isVine_erase_connected hX z b (mem_erase.mpr ⟨hbz,hX.1.2.2.1⟩) u hu⟩
    · exact Or.inl ⟨haz,isVine_erase_connected hX z a (mem_erase.mpr ⟨haz,hX.1.2.1⟩) u hu⟩
  | @append S T a b c n hS hT hi _hne ih =>
    obtain ⟨X,hX⟩ := hT
    have hs := chain_joints_mem hS
    have ht := hX.1
    have liftS : S.erase z ⊆ (S ∪ T).erase z := by
      intro v hv
      obtain ⟨hvz,hvS⟩ := mem_erase.mp hv
      exact mem_erase.mpr ⟨hvz,mem_union_left _ hvS⟩
    have liftT : T.erase z ⊆ (S ∪ T).erase z := by
      intro v hv
      obtain ⟨hvz,hvT⟩ := mem_erase.mp hv
      exact mem_erase.mpr ⟨hvz,mem_union_right _ hvT⟩
    intro u hu
    obtain ⟨huz,huU⟩ := mem_erase.mp hu
    by_cases hcz : c=z
    · have hcS : c ∉ S := by
        intro hcS
        have he : c=b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS,ht.2.2.1⟩)
        exact ht.2.2.2.1 he.symm
      have hSz : ∀ v ∈ S,v ≠ z := by
        intro v hv he
        exact hcS (hcz.symm ▸ he ▸ hv)
      have hbz := hSz b hs.2
      have haz := hSz a hs.1
      have liftS' : S ⊆ (S ∪ T).erase z := fun v hv => mem_erase.mpr ⟨hSz v hv,mem_union_left _ hv⟩
      refine Or.inl ⟨haz,?_⟩
      rcases mem_union.mp huU with huS | huT
      · exact induced_path_mono M liftS' (chain_connected hS a hs.1 u huS)
      · exact Relation.EqvGen.trans _ _ _
          (induced_path_mono M liftS' (chain_connected hS a hs.1 b hs.2))
          (induced_path_mono M liftT (isVine_erase_connected hX z b (mem_erase.mpr ⟨hbz,ht.2.1⟩) u
            (mem_erase.mpr ⟨huz,huT⟩)))
    · rcases mem_union.mp huU with huS | huT
      · rcases ih u (mem_erase.mpr ⟨huz,huS⟩) with ⟨haz,hp⟩ | ⟨hbz,hp⟩
        · exact Or.inl ⟨haz,induced_path_mono M liftS hp⟩
        · refine Or.inr ⟨hcz,Relation.EqvGen.trans _ _ _ ?_ (induced_path_mono M liftS hp)⟩
          exact induced_path_mono M liftT
            (isVine_erase_connected hX z c (mem_erase.mpr ⟨hcz,ht.2.2.1⟩) b (mem_erase.mpr ⟨hbz,ht.2.1⟩))
      · exact Or.inr ⟨hcz,induced_path_mono M liftT
          (isVine_erase_connected hX z c (mem_erase.mpr ⟨hcz,ht.2.2.1⟩) u (mem_erase.mpr ⟨huz,huT⟩))⟩

end WaveTurbulence.Vine

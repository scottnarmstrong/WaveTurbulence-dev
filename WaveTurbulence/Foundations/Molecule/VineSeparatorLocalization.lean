/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
import Mathlib.Tactic

/-! # A vine cannot cross a single-atom separation -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

omit [Fintype D] in
/-- A group connected after deletion of the separating atom lies on one
side of that separation. The closure premise is primitive adjacency data. -/
theorem connected_erase_subset_side (M : Molecule V D) (S T A : Finset V) (b : V)
    (hbS : b ∈ S) (hbT : b ∈ T) (hAU : A ⊆ S ∪ T)
    (hclosed : ∀ v ∈ T,v ≠ b → ∀ u ∈ S ∪ T,M.Adj v u → u ∈ T)
    (hconn : GroupConnected M (A.erase b)) : A ⊆ S ∨ A ⊆ T := by
  classical
  have inv {u v : V} (hp : (Mole.induced M (A.erase b)).SameComponent u v) :
      (u ∈ T ↔ v ∈ T) := by
    induction hp with
    | rel u v huv =>
      obtain ⟨hadj,hu,hv⟩ := (Mole.induced_adj_iff M (A.erase b) u v).mp huv
      obtain ⟨hub,huA⟩ := mem_erase.mp hu
      obtain ⟨hvb,hvA⟩ := mem_erase.mp hv
      exact ⟨fun huT => hclosed u huT hub v (hAU hvA) hadj,
        fun hvT => hclosed v hvT hvb u (hAU huA) (Mole.adj_symmetric M hadj)⟩
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  by_cases hAT : A ⊆ T
  · exact Or.inr hAT
  · obtain ⟨w,hwA,hwT⟩ := Finset.not_subset.mp hAT
    have hwb : w ≠ b := by intro he; exact hwT (he ▸ hbT)
    refine Or.inl (fun u huA => ?_)
    by_cases hub : u=b
    · exact hub ▸ hbS
    · have huT : u ∉ T := by
        intro huT
        exact hwT ((inv (hconn w (mem_erase.mpr ⟨hwb,hwA⟩) u (mem_erase.mpr ⟨hub,huA⟩))).mpr huT)
      exact (mem_union.mp (hAU huA)).resolve_right huT

/-- TARGET subsetvc's geometric localization step: a single actual vine
inside a block split at the initial joint of a terminal block cannot span
both sides. No gap or desired localization premise is assumed. -/
theorem vine_in_terminal_split (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {X : VineType}
    (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hbS : b ∈ S)
    (hA : M.IsVine X A x y) (hAU : A ⊆ S ∪ T) : A ⊆ S ∨ A ⊆ T := by
  apply connected_erase_subset_side M S T A b hbS hT.2.1 hAU
    (fun v hv hvb u hu huv => terminal_block_adj_mem M hM hT hU subset_union_right hv hvb hu huv)
  exact isVine_erase_connected hA b

end WaveTurbulence.Vine

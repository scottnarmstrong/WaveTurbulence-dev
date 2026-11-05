/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAdjointRemovalFamily
import Mathlib.Tactic

/-! # Simultaneous adjoint removals preserve connectivity -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

/-- TARGET subsetvc, simultaneous adjoint-removal clause: any disjoint
family of hyper-block adjoints can be removed from a connected atomic
group without disconnecting its remainder. All replacement paths are
constructed from the actual designated added bonds. -/
theorem simultaneous_adjoint_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    (S : Finset V) (hS : GroupConnected M S) (qs : List (AdjointPiece M))
    (hsub : ∀ P ∈ qs,P.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms S (qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms S (qs.map AdjointPiece.toRemoval),
        (removeBlocks M S (qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  apply removal_connected_of_joint_paths M S (qs.map AdjointPiece.toRemoval) hS
  · intro P hP Q hQ hne
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hQ
    exact hdis p hp q hq (fun he => hne (congrArg AdjointPiece.toRemoval he))
  · intro P hP d hd
    obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hP
    exact (mem_filter.mp (mem_sdiff.mp hd).1).2
  · intro P hP u hu v huv
    obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hP
    have hui := mem_sdiff.mp hu
    change u ∈ p.atoms ∧ u ∉ ({p.left,p.right} : Finset V) at hui
    have hne : u ≠ p.left ∧ u ≠ p.right := by
      simpa only [mem_insert,mem_singleton,not_or] using hui.2
    have hh : Mole.IsHyperBlock M p.atoms p.left p.right := ⟨p.added,p.ends_eq,p.adjoint_block⟩
    have hd := (Mole.hyperBlock_degrees M hh).2.2 u hui.1 hne.1 hne.2
    obtain ⟨d,hdu,hdv⟩ := huv
    have hc := Mole.full_degree_no_exit M hM (p.adjoint_block.1 hui.1) hd hdu
    exact hdv ▸ hc
  · intro P hP u hu v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
    let N := removeBlocks M S (qs.map AdjointPiece.toRemoval)
    have hk := adjointFamily_keep_added M S qs hsub hdis hp
    have he : (M.atom p.added=p.left ∧ M.atom (M.mate p.added)=p.right) ∨
        (M.atom p.added=p.right ∧ M.atom (M.mate p.added)=p.left) := Sym2.eq_iff.mp p.ends_eq
    have hadj : N.Adj p.left p.right := by
      rcases he with he | he
      · exact ⟨⟨p.added,hk⟩,he.1,he.2⟩
      · refine ⟨⟨M.mate p.added,keepDart_mate M S _ hk⟩,he.2,?_⟩
        change M.atom (M.mate (M.mate p.added))=p.right
        rw [M.mate_mate]
        exact he.1
    have hpath : N.SameComponent p.left p.right := Relation.EqvGen.rel _ _ hadj
    change u ∈ ({p.left,p.right} : Finset V) at hu
    change v ∈ ({p.left,p.right} : Finset V) at hv
    simp only [mem_insert,mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact hpath
    · exact Relation.EqvGen.symm _ _ hpath
    · exact Relation.EqvGen.refl _

end WaveTurbulence.Vine

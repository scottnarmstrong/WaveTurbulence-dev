/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMixedKeepAdded
public import WaveTurbulence.Foundations.Molecule.VineRemovalRetraction
import Mathlib.Tactic

/-! # Local adjoint retraction data remain valid after ordinary removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Disjoint actual adjoint pieces give disjoint removal-piece atom sets. -/
theorem adjoint_removal_family_disjoint (M : Molecule V D) (qs : List (AdjointPiece M))
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ P ∈ qs.map AdjointPiece.toRemoval,∀ Q ∈ qs.map AdjointPiece.toRemoval,
      P ≠ Q → Disjoint P.atoms Q.atoms := by
  intro P hP Q hQ hne
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hQ
  exact hdis p hp q hq (fun he => hne (congrArg AdjointPiece.toRemoval he))

/-- Every selected adjoint dart belongs to its actual atom group. -/
theorem adjoint_removal_family_inside (M : Molecule V D) (qs : List (AdjointPiece M)) :
    ∀ P ∈ qs.map AdjointPiece.toRemoval,∀ d ∈ P.darts,M.InGroup P.atoms d := by
  intro P hP d hd
  obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hP
  exact (mem_filter.mp (mem_sdiff.mp hd).1).2

/-- An adjoint's nonjoint atoms have full original degree and no exiting
edge. This uses the original molecule, not an intermediate removal graph. -/
theorem adjoint_removal_family_closed (M : Molecule V D) (hM : M.IsMolecule)
    (qs : List (AdjointPiece M)) :
    ∀ P ∈ qs.map AdjointPiece.toRemoval,∀ u ∈ P.interior,∀ v,M.Adj u v → v ∈ P.atoms := by
  intro P hP u hu v huv
  obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hP
  have hui := mem_sdiff.mp hu
  change u ∈ p.atoms ∧ u ∉ ({p.left,p.right} : Finset V) at hui
  have hne : u ≠ p.left ∧ u ≠ p.right := by
    simpa only [mem_insert,mem_singleton,not_or] using hui.2
  have hH : Mole.IsHyperBlock M p.atoms p.left p.right := ⟨p.added,p.ends_eq,p.adjoint_block⟩
  have hd := (Mole.hyperBlock_degrees M hH).2.2 u hui.1 hne.1 hne.2
  obtain ⟨d,hdu,hdv⟩ := huv
  have hc := Mole.full_degree_no_exit M hM (p.adjoint_block.1 hui.1) hd hdu
  exact hdv ▸ hc

/-- Each adjoint's two retraction joints are joined by the designated
added bond after the complete ordinary and adjoint family is removed. -/
theorem mixed_adjoint_joint_paths (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hsub : ∀ Q ∈ qs,Q.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d) :
    ∀ P ∈ qs.map AdjointPiece.toRemoval,∀ u ∈ ({P.left,P.right} : Finset V),
      ∀ v ∈ ({P.left,P.right} : Finset V),
        (removeBlocks M S (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  intro P hP u hu v hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
  let N := removeBlocks M S (ps++qs.map AdjointPiece.toRemoval)
  have hk := mixedFamily_keep_added M S ps qs hsub hdis hcross hinside hp
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

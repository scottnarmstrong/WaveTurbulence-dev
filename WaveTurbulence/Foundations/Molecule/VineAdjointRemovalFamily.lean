/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemovalConnectivity
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Surviving added bonds for disjoint families of adjoint removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

/-- An actual hyper-block with its designated added bond. These are the
witnesses of the pinned adjoint construction, with no extra graph premise. -/
structure AdjointPiece (M : Molecule V D) where
  atoms : Finset V
  left : V
  right : V
  added : D
  ends_eq : M.ends added=s(left,right)
  adjoint_block : (Mole.eraseBond M added).IsBlock atoms left right

/-- The source removal attached to an actual adjoint witness. -/
@[expose] def AdjointPiece.toRemoval {M : Molecule V D} (P : AdjointPiece M) : RemovalPiece V D :=
  adjointRemoval M P.atoms P.left P.right P.added

/-- Every joint of a piece survives a disjoint family of adjoint removals. -/
theorem adjointFamily_joint_mem (M : Molecule V D) (S : Finset V) (qs : List (AdjointPiece M))
    (hsub : ∀ P ∈ qs,P.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    {P : AdjointPiece M} (hP : P ∈ qs) {v : V} (hv : v=P.left ∨ v=P.right) :
    v ∈ remainingAtoms S (qs.map AdjointPiece.toRemoval) := by
  have hvP : v ∈ P.atoms := hv.elim (fun h => h.symm ▸ P.adjoint_block.2.1)
    (fun h => h.symm ▸ P.adjoint_block.2.2.1)
  refine mem_filter.mpr ⟨hsub P hP hvP,?_⟩
  intro R hR
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
  by_cases he : P=Q
  · subst Q
    intro hi
    have hh := (mem_sdiff.mp hi).2
    apply hh
    simpa only [AdjointPiece.toRemoval,adjointRemoval,mem_insert,mem_singleton] using hv
  · intro hi
    exact Finset.disjoint_left.mp (hdis P hP Q hQ he) hvP (mem_sdiff.mp hi).1

/-- Each designated added bond survives all the disjoint adjoint removals,
not only its own removal. -/
theorem adjointFamily_keep_added (M : Molecule V D) (S : Finset V) (qs : List (AdjointPiece M))
    (hsub : ∀ P ∈ qs,P.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    {P : AdjointPiece M} (hP : P ∈ qs) :
    KeepDart M S (qs.map AdjointPiece.toRemoval) P.added := by
  have hend : (M.atom P.added=P.left ∧ M.atom (M.mate P.added)=P.right) ∨
      (M.atom P.added=P.right ∧ M.atom (M.mate P.added)=P.left) := Sym2.eq_iff.mp P.ends_eq
  have hx : M.atom P.added=P.left ∨ M.atom P.added=P.right := hend.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hy : M.atom (M.mate P.added)=P.left ∨ M.atom (M.mate P.added)=P.right := hend.elim
    (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  refine ⟨adjointFamily_joint_mem M S qs hsub hdis hP hx,
    adjointFamily_joint_mem M S qs hsub hdis hP hy,?_⟩
  intro R hR
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
  by_cases he : P=Q
  · subst Q
    constructor <;> simp [AdjointPiece.toRemoval,adjointRemoval]
  · have hxP : M.atom P.added ∈ P.atoms := hx.elim
      (fun h => h.symm ▸ P.adjoint_block.2.1) (fun h => h.symm ▸ P.adjoint_block.2.2.1)
    have hyP : M.atom (M.mate P.added) ∈ P.atoms := hy.elim
      (fun h => h.symm ▸ P.adjoint_block.2.1) (fun h => h.symm ▸ P.adjoint_block.2.2.1)
    constructor
    · intro hm
      have hh := (mem_filter.mp (mem_sdiff.mp hm).1).2.1
      exact Finset.disjoint_left.mp (hdis P hP Q hQ he) hxP hh
    · intro hm
      have hh := (mem_filter.mp (mem_sdiff.mp hm).1).2.1
      exact Finset.disjoint_left.mp (hdis P hP Q hQ he) hyP hh

end WaveTurbulence.Vine

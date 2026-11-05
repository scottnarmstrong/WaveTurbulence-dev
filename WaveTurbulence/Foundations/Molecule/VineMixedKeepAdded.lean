/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAdjointRemovalFamily
public import WaveTurbulence.Foundations.Molecule.VineRemovalAppend
import Mathlib.Tactic

/-! # Designated added bonds survive disjoint ordinary and adjoint removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every endpoint of the designated added bond belongs to its actual piece. -/
theorem AdjointPiece.added_inGroup {M : Molecule V D} (P : AdjointPiece M) : M.InGroup P.atoms P.added := by
  rcases Sym2.eq_iff.mp P.ends_eq with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ⟨hx.symm ▸ P.adjoint_block.2.1,hy.symm ▸ P.adjoint_block.2.2.1⟩
  · exact ⟨hx.symm ▸ P.adjoint_block.2.2.1,hy.symm ▸ P.adjoint_block.2.1⟩

/-- A designated added bond survives the simultaneous ordinary family
and the entire disjoint adjoint family. Ordinary darts are actual internal
bonds and their atom groups are disjoint from every adjoint piece. -/
theorem mixedFamily_keep_added (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hsub : ∀ Q ∈ qs,Q.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d)
    {Q : AdjointPiece M} (hQ : Q ∈ qs) :
    KeepDart M S (ps++qs.map AdjointPiece.toRemoval) Q.added := by
  apply (keepDart_append_iff M S ps _ Q.added).mpr
  refine ⟨?_,adjointFamily_keep_added M S qs hsub hdis hQ⟩
  have hg := Q.added_inGroup
  have survive (v : V) (hv : v ∈ Q.atoms) : v ∈ remainingAtoms S ps := by
    refine mem_filter.mpr ⟨hsub Q hQ hv,?_⟩
    intro P hP hi
    exact (disjoint_left.mp (hcross P hP Q hQ)) (mem_sdiff.mp hi).1 hv
  refine ⟨survive _ hg.1,survive _ hg.2,?_⟩
  intro P hP
  constructor
  · intro hd
    exact (disjoint_left.mp (hcross P hP Q hQ)) (hinside P hP Q.added hd).1 hg.1
  · intro hd
    exact (disjoint_left.mp (hcross P hP Q hQ)) (hinside P hP (M.mate Q.added) hd).1 hg.2

end WaveTurbulence.Vine

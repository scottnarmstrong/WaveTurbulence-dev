/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Retraction of disjoint removed interiors to their retained joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V]

/-- Map every removed interior to its piece's left joint; keep every
surviving atom fixed. Disjointness makes the choice of piece immaterial. -/
@[expose] noncomputable def removalRetraction (ps : List (RemovalPiece V D)) (v : V) : V := by
  classical
  exact if h : ∃ P,P ∈ ps ∧ v ∈ P.interior then (Classical.choose h).left else v

/-- Surviving atoms are fixed by the removal retraction. -/
theorem removalRetraction_fixed (S : Finset V) (ps : List (RemovalPiece V D))
    {v : V} (hv : v ∈ remainingAtoms S ps) : removalRetraction ps v=v := by
  classical
  have hn : ¬∃ P,P ∈ ps ∧ v ∈ P.interior := by
    rintro ⟨P,hP,hvP⟩
    exact (mem_filter.mp hv).2 P hP hvP
  simp only [removalRetraction,hn,dite_false]

/-- Every atom of a removed piece retracts to one of that piece's joints,
even when many disjoint pieces are removed simultaneously. -/
theorem removalRetraction_joint (ps : List (RemovalPiece V D))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    {P : RemovalPiece V D} (hP : P ∈ ps) {v : V} (hv : v ∈ P.atoms) :
    removalRetraction ps v ∈ ({P.left,P.right} : Finset V) := by
  classical
  by_cases hi : ∃ Q,Q ∈ ps ∧ v ∈ Q.interior
  · have hQ := Classical.choose_spec hi
    have he : Classical.choose hi=P := by
      by_contra hne
      have hd := hdis _ hQ.1 P hP hne
      exact (Finset.disjoint_left.mp hd) (mem_sdiff.mp hQ.2).1 hv
    simp only [removalRetraction,hi,dite_true,he,mem_insert_self]
  · have hj : v ∈ ({P.left,P.right} : Finset V) := by
      by_contra hh
      exact hi ⟨P,hP,mem_sdiff.mpr ⟨hv,hh⟩⟩
    simpa only [removalRetraction,hi,dite_false] using hj

end WaveTurbulence.Vine

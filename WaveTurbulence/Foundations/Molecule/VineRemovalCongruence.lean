/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Removal families depend on atom groups, unordered joints and selected darts -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V]

/-- Two removal presentations carry identical source atom and bond data,
allowing their two joints to be interchanged. -/
@[expose] def RemovalPiece.Equivalent (P Q : RemovalPiece V D) : Prop :=
  P.atoms=Q.atoms ∧ ({P.left,P.right} : Finset V)={Q.left,Q.right} ∧ P.darts=Q.darts

/-- Interchanging equivalent removal presentations is symmetric. -/
theorem RemovalPiece.Equivalent.symm {P Q : RemovalPiece V D} (h : P.Equivalent Q) :
    Q.Equivalent P := ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩

/-- Equivalent pieces delete the same nonjoint atoms. -/
theorem RemovalPiece.Equivalent.interior_eq {P Q : RemovalPiece V D} (h : P.Equivalent Q) :
    P.interior=Q.interior := by
  simp only [RemovalPiece.interior,h.1,h.2.1]

/-- Equivalent families have the same removal data, allowing repetitions
and different ordering. Each occurrence has a matching equivalent piece. -/
@[expose] def RemovalFamilyEquivalent (ps qs : List (RemovalPiece V D)) : Prop :=
  (∀ P ∈ ps,∃ Q ∈ qs,P.Equivalent Q) ∧ (∀ Q ∈ qs,∃ P ∈ ps,P.Equivalent Q)

/-- Family equivalence is symmetric. -/
theorem RemovalFamilyEquivalent.symm {ps qs : List (RemovalPiece V D)}
    (h : RemovalFamilyEquivalent ps qs) : RemovalFamilyEquivalent qs ps := by
  constructor
  · intro Q hQ
    obtain ⟨P,hP,he⟩ := h.2 Q hQ
    exact ⟨P,hP,he.symm⟩
  · intro P hP
    obtain ⟨Q,hQ,he⟩ := h.1 P hP
    exact ⟨Q,hQ,he.symm⟩

/-- Presentation changes do not affect the surviving atom set. -/
theorem remainingAtoms_congr_of_equivalent (S : Finset V) {ps qs : List (RemovalPiece V D)}
    (h : RemovalFamilyEquivalent ps qs) : remainingAtoms S ps=remainingAtoms S qs := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvS,hvp⟩ := mem_filter.mp hv
    refine mem_filter.mpr ⟨hvS,?_⟩
    intro Q hQ
    obtain ⟨P,hP,he⟩ := h.2 Q hQ
    rw [← he.interior_eq]
    exact hvp P hP
  · intro hv
    obtain ⟨hvS,hvq⟩ := mem_filter.mp hv
    refine mem_filter.mpr ⟨hvS,?_⟩
    intro P hP
    obtain ⟨Q,hQ,he⟩ := h.1 P hP
    rw [he.interior_eq]
    exact hvq Q hQ

/-- Presentation changes preserve every surviving actual dart. -/
theorem keepDart_iff_of_equivalent (M : Molecule V D) (S : Finset V)
    {ps qs : List (RemovalPiece V D)} (h : RemovalFamilyEquivalent ps qs) (d : D) :
    KeepDart M S ps d ↔ KeepDart M S qs d := by
  have hr := remainingAtoms_congr_of_equivalent S h
  constructor
  · rintro ⟨hu,hv,hd⟩
    refine ⟨hr ▸ hu,hr ▸ hv,?_⟩
    intro Q hQ
    obtain ⟨P,hP,he⟩ := h.2 Q hQ
    rw [← he.2.2]
    exact hd P hP
  · rintro ⟨hu,hv,hd⟩
    refine ⟨hr.symm ▸ hu,hr.symm ▸ hv,?_⟩
    intro P hP
    obtain ⟨Q,hQ,he⟩ := h.1 P hP
    rw [he.2.2]
    exact hd Q hQ

/-- Every surviving path transports across equivalent removal-family
presentations, keeping the original dart and involution identities. -/
theorem removal_path_congr_of_equivalent (M : Molecule V D) (S : Finset V)
    {ps qs : List (RemovalPiece V D)} (h : RemovalFamilyEquivalent ps qs)
    {u v : V} (hp : (removeBlocks M S ps).SameComponent u v) :
    (removeBlocks M S qs).SameComponent u v := by
  induction hp with
  | rel u v huv =>
    obtain ⟨d,hdu,hdv⟩ := huv
    have hk := (keepDart_iff_of_equivalent M S h d.1).mp d.2
    exact Relation.EqvGen.rel _ _ ⟨⟨d.1,hk⟩,hdu,hdv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine

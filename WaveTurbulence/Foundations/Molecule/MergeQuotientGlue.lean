/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MergeQuotients
import Mathlib.Tactic

/-! # Collapsing an attached group at a unique joint
The quotient equivalence is constructed from a concrete retraction and
inclusion. It is the atom-carrier induction used by chain splicing.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V : Type*} [DecidableEq V]

@[expose] def mergeGlueBackward (X A : Finset V) (groups : List (Finset V)) :
    MergeQuotient X groups → MergeQuotient (X ∪ A) (A :: groups) :=
  mergeQuotientLift (fun v => mergeClass (X ∪ A) (A :: groups) ⟨v.1,mem_union_left A v.2⟩) (by
    intro u v h
    obtain ⟨S,hS,hu,hv⟩ := h
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨S,List.mem_cons_of_mem _ hS,hu,hv⟩))

@[expose] def mergeGlueForward (X A : Finset V) (c : V) (groups : List (Finset V))
    (hcX : c ∈ X) (hi : X ∩ A = {c}) (hsub : ∀ S ∈ groups, S ⊆ X) :
    MergeQuotient (X ∪ A) (A :: groups) → MergeQuotient X groups :=
  mergeQuotientLift (fun v => mergeClass X groups (unionJointRetraction X A c hcX v)) (by
    intro u v h
    obtain ⟨S,hS,hu,hv⟩ := h
    rcases List.mem_cons.mp hS with he | hS
    · subst S
      rw [unionJointRetraction_attached X A c hcX hi u hu,
        unionJointRetraction_attached X A c hcX hi v hv]
    · have huX := hsub S hS hu
      have hvX := hsub S hS hv
      rw [unionJointRetraction_inside X A c hcX u huX,
        unionJointRetraction_inside X A c hcX v hvX]
      exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨S,hS,hu,hv⟩))

theorem mergeGlueBackward_class (X A : Finset V) (groups : List (Finset V)) (v : ↥X) :
    mergeGlueBackward X A groups (mergeClass X groups v) =
      mergeClass (X ∪ A) (A :: groups) ⟨v.1,mem_union_left A v.2⟩ := rfl

theorem mergeGlueForward_class (X A : Finset V) (c : V) (groups : List (Finset V))
    (hcX : c ∈ X) (hi : X ∩ A = {c}) (hsub : ∀ S ∈ groups, S ⊆ X) (v : ↥(X ∪ A)) :
    mergeGlueForward X A c groups hcX hi hsub (mergeClass (X ∪ A) (A :: groups) v) =
      mergeClass X groups (unionJointRetraction X A c hcX v) := rfl

@[expose] def mergeQuotientGlue (X A : Finset V) (c : V) (groups : List (Finset V))
    (hcX : c ∈ X) (hcA : c ∈ A) (hi : X ∩ A = {c}) (hsub : ∀ S ∈ groups, S ⊆ X) :
    MergeQuotient (X ∪ A) (A :: groups) ≃ MergeQuotient X groups where
  toFun := mergeGlueForward X A c groups hcX hi hsub
  invFun := mergeGlueBackward X A groups
  left_inv q := by
    induction q using Quotient.inductionOn with | h v =>
      change mergeGlueBackward X A groups
        (mergeGlueForward X A c groups hcX hi hsub (mergeClass (X ∪ A) (A :: groups) v)) =
          mergeClass (X ∪ A) (A :: groups) v
      rw [mergeGlueForward_class,mergeGlueBackward_class]
      by_cases hv : v.1 ∈ X
      · rw [unionJointRetraction_inside X A c hcX v hv]
      · have hvA := (mem_union.mp v.2).resolve_left hv
        have hr : unionJointRetraction X A c hcX v = ⟨c,hcX⟩ := dite_eq_right hv
        rw [hr]
        exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨A,List.mem_cons_self,hcA,hvA⟩)
  right_inv q := by
    induction q using Quotient.inductionOn with | h v =>
      change mergeGlueForward X A c groups hcX hi hsub
        (mergeGlueBackward X A groups (mergeClass X groups v)) = mergeClass X groups v
      rw [mergeGlueBackward_class,mergeGlueForward_class,
        unionJointRetraction_inside X A c hcX _ v.2]

theorem mergeQuotientGlue_old_class (X A : Finset V) (c : V) (groups : List (Finset V))
    (hcX : c ∈ X) (hcA : c ∈ A) (hi : X ∩ A = {c}) (hsub : ∀ S ∈ groups, S ⊆ X) (v : ↥X) :
    mergeQuotientGlue X A c groups hcX hcA hi hsub
      (mergeClass (X ∪ A) (A :: groups) ⟨v.1,mem_union_left A v.2⟩) = mergeClass X groups v := by
  simp only [mergeQuotientGlue,Equiv.coe_fn_mk]
  rw [mergeGlueForward_class,unionJointRetraction_inside X A c hcX _ v.2]

@[expose] def mergeQuotientEmptyEquiv (X : Finset V) : MergeQuotient X [] ≃ ↥X where
  toFun := mergeQuotientLift id (by
    rintro u v ⟨S,hS,_hu,_hv⟩
    exact (List.not_mem_nil hS).elim)
  invFun := mergeClass X []
  left_inv q := by induction q using Quotient.inductionOn with | h v => rfl
  right_inv v := rfl

end WaveTurbulence.Mole

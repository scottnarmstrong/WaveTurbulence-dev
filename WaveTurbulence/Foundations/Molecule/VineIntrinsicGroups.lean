/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoubleGroupRecognition
public import WaveTurbulence.Foundations.Molecule.VineIntrinsicCoreGroups
import Mathlib.Tactic

/-! # Intrinsic relations used to recover vine coherence groups -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual nonjoint atoms, with no reference to template labels. -/
@[expose] def VineInterior (S : Finset V) (a b u : V) : Prop :=
  u ∈ S ∧ u ≠ a ∧ u ≠ b

/-- An intrinsic doubled pair of distinct nonjoint atoms. -/
@[expose] def CoherenceDouble (M : Molecule V D) (S : Finset V) (a b u v : V) : Prop :=
  VineInterior S a b u ∧ VineInterior S a b v ∧ u ≠ v ∧ Nonempty (TwoIncidences M u v)

/-- A nonjoint atom without a nonjoint doubled partner. -/
@[expose] def CoherenceUndoubled (M : Molecule V D) (S : Finset V) (a b u : V) : Prop :=
  VineInterior S a b u ∧ ∀ v,¬CoherenceDouble M S a b u v

/-- Intrinsic group-generating edges. The second clause joins the VII
exceptional pair; the third attaches III's undoubled atom to its triangle. -/
@[expose] def CoherenceEdge (M : Molecule V D) (S : Finset V) (a b u v : V) : Prop :=
  CoherenceDouble M S a b u v ∨
  (CoherenceUndoubled M S a b u ∧ CoherenceUndoubled M S a b v) ∨
  (CoherenceUndoubled M S a b u ∧ ∃ w,CoherenceDouble M S a b v w ∧ M.Adj u v ∧ M.Adj u w)

/-- A fresh atom has a distinct doubled partner and cannot be undoubled. -/
theorem VineRealization.undoubled_old (M : Molecule V D)
    {X : VineType} {S : Finset V} {a b u : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (hu : CoherenceUndoubled M S a b u) : R.f u<X.template.n := by
  by_contra h
  obtain ⟨A,i,hi,hin,he⟩ := R.fresh_slot hu.1.1 (by omega)
  have hnon (v : V) (hv : v ∈ S) (hf : X.template.n ≤ R.f v) : VineInterior S a b v := by
    have hn : 2 ≤ X.template.n := by cases X <;> decide
    have hh := realization_index_lt_two_iff R hB hv
    have hn' : ¬(v=a ∨ v=b) := fun h => by have := hh.mpr h; omega
    exact ⟨hv,not_or.mp hn'⟩
  have hN : X.template.n ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]; omega
  have hU := hnon (A.Q.u i) (A.mem i).1 (by rw [(A.labels i hi hin).1]; omega)
  have hV := hnon (A.Q.v i) (A.mem i).2 (by rw [(A.labels i hi hin).2]; omega)
  have hne := A.frame.upper_cross i i hi hin (by omega)
  rcases he with rfl | rfl
  · exact hu.2 _ ⟨hU,hV,hne,⟨A.double i hi hin⟩⟩
  · exact hu.2 _ ⟨hV,hU,hne.symm,⟨(A.double i hi hin).mates⟩⟩

end WaveTurbulence.Vine

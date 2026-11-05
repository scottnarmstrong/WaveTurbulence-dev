/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
import Mathlib.Tactic

/-! # Source slot sequences with all four old rail endpoints retained -/

public section
namespace WaveTurbulence.Vine

/-- The full expansion has the chosen slot sequence with exactly the
original slot endpoints and exact allocated interior labels. -/
theorem expand_has_insertedSequence_ports (X : VineType) (ks : List ℕ)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip ks=pre++(s,k)::post) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template
    ∃ L : LiteralFullRungSequence (X.expand ks) k,
      ((L.u 0).1=s.1.1 ∧ (L.v 0).1=s.2.1 ∧
        (L.u (k+1)).1=s.1.2 ∧ (L.v (k+1)).1=s.2.2) ∧
      ∀ i,1 ≤ i → i ≤ k → (L.u i).1=U.n+(i-1) ∧ (L.v i).1=U.n+k+(i-1) := by
  have hh := fold_has_insertedSequence_ports X.template pre post s k (template_endpoints X) (by
    intro sk hsk
    rw [← hloc] at hsk
    exact template_slot_endpoints X sk.1 (List.of_mem_zip hsk).1)
  rw [← hloc] at hh
  exact hh

/-- Every actual slot has its four original endpoint labels as well as
its allocated interior labels. All sequence values belong to the outer vine. -/
theorem VineRealization.has_rungSequence_ports {V D : Type*} [DecidableEq V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template
    ∃ Q : FullRungSequence M k,(∀ i,Q.u i ∈ S ∧ Q.v i ∈ S) ∧
      (R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
        R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2) ∧
      ∀ i,1 ≤ i → i ≤ k → R.f (Q.u i)=U.n+(i-1) ∧ R.f (Q.v i)=U.n+k+(i-1) := by
  obtain ⟨L,hports,hL⟩ := expand_has_insertedSequence_ports X R.k pre post s k hloc
  refine ⟨L.realize R,fun i => ⟨(R.atomAt (L.u i)).2,(R.atomAt (L.v i)).2⟩,?_,?_⟩
  · exact ⟨(R.label_atomAt (L.u 0)).trans hports.1,
      (R.label_atomAt (L.v 0)).trans hports.2.1,
      (R.label_atomAt (L.u (k+1))).trans hports.2.2.1,
      (R.label_atomAt (L.v (k+1))).trans hports.2.2.2⟩
  · intro i hi hin
    exact ⟨(R.label_atomAt (L.u i)).trans (hL i hi hin).1,
      (R.label_atomAt (L.v i)).trans (hL i hi hin).2⟩

end WaveTurbulence.Vine

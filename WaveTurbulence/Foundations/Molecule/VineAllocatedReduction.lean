/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
public import WaveTurbulence.Foundations.Molecule.VineRungJointExclusion
import Mathlib.Tactic

/-! # Actual block reduction on the allocated interval of a long slot -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- The two rail label intervals exhaust exactly the fresh allocated atoms. -/
theorem allocatedSequence_covers (M : Molecule V D) (S : Finset V) (f : V → ℕ)
    (hf : Set.InjOn f S) {k N : ℕ} (Q : FullRungSequence M k)
    (hQ : ∀ i,1 ≤ i → i ≤ k → Q.u i ∈ S ∧ Q.v i ∈ S ∧
      f (Q.u i)=N+(i-1) ∧ f (Q.v i)=N+k+(i-1)) {v : V} (hv : v ∈ S)
    (hlo : N ≤ f v) (hhi : f v<N+2*k) :
    ∃ i,1 ≤ i ∧ i ≤ k ∧ (v=Q.u i ∨ v=Q.v i) := by
  by_cases hu : f v<N+k
  · let i := f v-N+1
    have hi : 1 ≤ i := by dsimp only [i]; omega
    have hin : i ≤ k := by dsimp only [i]; omega
    have hh := hQ i hi hin
    refine ⟨i,hi,hin,Or.inl (hf hv hh.1 ?_)⟩
    rw [hh.2.2.1]
    dsimp only [i]
    omega
  · let i := f v-(N+k)+1
    have hi : 1 ≤ i := by dsimp only [i]; omega
    have hin : i ≤ k := by dsimp only [i]; omega
    have hh := hQ i hi hin
    refine ⟨i,hi,hin,Or.inr (hf hv hh.2.1 ?_)⟩
    rw [hh.2.2.2]
    dsimp only [i]
    omega

/-- TARGET subsetvc, actual long-slot reduction: a connected block larger
than a double bond has a constant membership bit throughout every inserted
slot of length at least three, and none of these fresh atoms is its joint.
The conclusion is derived directly from the pinned vine realization. -/
theorem block_long_slot_reduction (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {p q : V} (hB : M.IsBlock A p q) (hC : GroupConnected M A)
    (hcard : 2<A.card) (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (hk : 3 ≤ k)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    ∃ w ∈ S,R.f w=N ∧ ∀ v ∈ S,N ≤ R.f v → R.f v<N+2*k →
      (v ∈ A ↔ w ∈ A) ∧ v ≠ p ∧ v ≠ q := by
  obtain ⟨Q,hQ⟩ := R.has_rungSequence pre post s k hloc
  dsimp only at hQ ⊢
  have h1 := hQ 1 (by omega) (by omega)
  refine ⟨Q.u 1,h1.1,?_,?_⟩
  · simpa only [Nat.sub_self,Nat.add_zero] using h1.2.2.1
  · intro v hv hlo hhi
    obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q hQ hv hlo hhi
    have hc := block_fullRungSequence_constant M hM hB hC hcard hk Q i hi hin 1 (by omega) (by omega)
    have hp := block_fullRungSequence_membership M hM hB hk Q i hi hin
    have hj := block_fullRungSequence_no_joints M hM hB hC hcard hk Q i hi hin
    rcases he with rfl | rfl
    · exact ⟨hc,hj.1⟩
    · exact ⟨hp.symm.trans hc,hj.2⟩

end WaveTurbulence.Vine

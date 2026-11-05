/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperSequenceTransitions
import Mathlib.Tactic

/-! # Finite-interval membership masks with at most one jump -/

public section
namespace WaveTurbulence.Vine

/-- Adjacent equivalences propagate over an arbitrary natural interval. -/
theorem interval_iff_of_steps (P : ℕ → Prop) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ i,a ≤ i → i<b → (P i ↔ P (i+1))) : P a ↔ P b := by
  have hh : ∀ i,a ≤ i → i ≤ b → (P a ↔ P i) := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base => intro _; exact Iff.rfl
    | succ i hi ih =>
      intro hin
      exact (ih (by omega)).trans (hstep i hi (by omega))
  exact hh b hab le_rfl

/-- A finite mask with at most one adjacent change is constant, or is a
prefix followed by its complementary suffix. No bound on the length is used. -/
theorem one_jump_mask (P : ℕ → Prop) (n : ℕ)
    (hunique : ∀ i j,1 ≤ i → i+1 ≤ n → 1 ≤ j → j+1 ≤ n →
      ¬(P i ↔ P (i+1)) → ¬(P j ↔ P (j+1)) → i=j) :
    (∀ i,1 ≤ i → i ≤ n → (P i ↔ P 1)) ∨
      ∃ t,1 ≤ t ∧ t+1 ≤ n ∧ ∀ i,1 ≤ i → i ≤ n →
        (P i ↔ if i ≤ t then P 1 else ¬P 1) := by
  classical
  by_cases hjump : ∃ t,1 ≤ t ∧ t+1 ≤ n ∧ ¬(P t ↔ P (t+1))
  · obtain ⟨t,ht,htn,hjump⟩ := hjump
    have hleft : ∀ i,1 ≤ i → i ≤ t → (P i ↔ P 1) := by
      intro i hi hin
      symm
      apply interval_iff_of_steps P 1 i hi
      intro j hj hjn
      by_contra hn
      have he := hunique j t hj (by omega) ht htn hn hjump
      omega
    have hneg : P (t+1) ↔ ¬P 1 := by
      have hh := hleft t ht le_rfl
      tauto
    refine Or.inr ⟨t,ht,htn,?_⟩
    intro i hi hin
    by_cases hit : i ≤ t
    · simp only [hit,ite_true]
      exact hleft i hi hit
    · simp only [hit,ite_false]
      have hh : P (t+1) ↔ P i := by
        apply interval_iff_of_steps P (t+1) i (by omega)
        intro j hj hjn
        by_contra hn
        have he := hunique j t (by omega) (by omega) ht htn hn hjump
        omega
      exact hh.symm.trans hneg
  · refine Or.inl ?_
    intro i hi hin
    symm
    apply interval_iff_of_steps P 1 i hi
    intro j hj hjn
    by_contra hn
    exact hjump ⟨j,hj,by omega,hn⟩

/-- TARGET subsetvc, hyper-block mask reduction on actual full rungs:
for every length the selected rungs are constant, or a prefix followed by
its complementary suffix. The transition uniqueness is proved from the
two source joints and actual incidences. -/
theorem hyperBlock_fullRungSequence_mask {V D : Type*} [DecidableEq V]
    [Fintype D] [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n : ℕ}
    (Q : FullRungSequence M n) :
    (∀ i,1 ≤ i → i ≤ n → (Q.u i ∈ A ↔ Q.u 1 ∈ A)) ∨
      ∃ t,1 ≤ t ∧ t+1 ≤ n ∧ ∀ i,1 ≤ i → i ≤ n →
        (Q.u i ∈ A ↔ if i ≤ t then Q.u 1 ∈ A else Q.u 1 ∉ A) := by
  apply one_jump_mask (fun i => Q.u i ∈ A) n
  intro i j hi hin hj hjn hji hjj
  exact hyperBlock_sequence_jump_unique M hM hH Q hi hin hj hjn hji hjj

end WaveTurbulence.Vine

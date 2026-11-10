/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
public import WaveTurbulence.Foundations.Molecule.VineRungTransitions
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

end WaveTurbulence.Vine

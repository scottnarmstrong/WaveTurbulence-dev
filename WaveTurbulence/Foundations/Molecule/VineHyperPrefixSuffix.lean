/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperGapInterval
import Mathlib.Tactic

/-! # A hyper-block selects a prefix or suffix from a ladder with an absent far port -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- If the far endpoint pair is absent, the selected full rungs form one
prefix, possibly empty. The cutoff is constructed from the actual selected
indices, without a positivity or fixed-length restriction. -/
theorem hyperBlock_sequence_prefix (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n : ℕ}
    (Q : FullRungSequence M n) (huN : Q.u (n+1) ∉ A) (hvN : Q.v (n+1) ∉ A) :
    ∃ t,t ≤ n ∧ ∀ i,1 ≤ i → i ≤ n → (Q.u i ∈ A ↔ i ≤ t) := by
  let T := (Icc 1 n).filter (fun i => Q.u i ∈ A)
  by_cases hne : T.Nonempty
  · let t := T.max' hne
    have ht := mem_filter.mp (max'_mem T hne)
    have htb := mem_Icc.mp ht.1
    refine ⟨t,htb.2,?_⟩
    intro i hi hin
    constructor
    · intro hxi
      exact le_max' T i (mem_filter.mpr ⟨mem_Icc.mpr ⟨hi,hin⟩,hxi⟩)
    · intro hit
      by_contra hxi
      have hvi : Q.v i ∉ A := fun hv => hxi
        ((hyperBlock_sequence_pair_membership M hM hH Q i hi hin).mpr hv)
      have hit' : i < t := by
        by_contra hh
        have he : i=t := by omega
        exact hxi (he.symm ▸ ht.2)
      have hh := hyperBlock_absent_interval M hM hH Q i (n+1) (by omega) le_rfl
        hxi hvi huN hvN t hit' (by omega)
      exact hh.1 ht.2
  · refine ⟨0,by omega,?_⟩
    intro i hi hin
    constructor
    · intro hxi
      exact False.elim (hne ⟨i,mem_filter.mpr ⟨mem_Icc.mpr ⟨hi,hin⟩,hxi⟩⟩)
    · intro hbad
      omega

/-- If the initial endpoint pair is absent, the selected full rungs form
one suffix, possibly empty. The threshold may equal n+1. -/
theorem hyperBlock_sequence_suffix (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n : ℕ}
    (Q : FullRungSequence M n) (hu0 : Q.u 0 ∉ A) (hv0 : Q.v 0 ∉ A) :
    ∃ t,1 ≤ t ∧ t ≤ n+1 ∧ ∀ i,1 ≤ i → i ≤ n → (Q.u i ∈ A ↔ t ≤ i) := by
  let T := (Icc 1 n).filter (fun i => Q.u i ∈ A)
  by_cases hne : T.Nonempty
  · let t := T.min' hne
    have ht := mem_filter.mp (min'_mem T hne)
    have htb := mem_Icc.mp ht.1
    refine ⟨t,htb.1,by omega,?_⟩
    intro i hi hin
    constructor
    · intro hxi
      exact min'_le T i (mem_filter.mpr ⟨mem_Icc.mpr ⟨hi,hin⟩,hxi⟩)
    · intro hti
      by_contra hxi
      have hvi : Q.v i ∉ A := fun hv => hxi
        ((hyperBlock_sequence_pair_membership M hM hH Q i hi hin).mpr hv)
      have hti' : t < i := by
        by_contra hh
        have he : i=t := by omega
        exact hxi (he.symm ▸ ht.2)
      have hh := hyperBlock_absent_interval M hM hH Q 0 i (by omega) (by omega)
        hu0 hv0 hxi hvi t (by omega) hti'
      exact hh.1 ht.2
  · refine ⟨n+1,by omega,le_rfl,?_⟩
    intro i hi hin
    constructor
    · intro hxi
      exact False.elim (hne ⟨i,mem_filter.mpr ⟨mem_Icc.mpr ⟨hi,hin⟩,hxi⟩⟩)
    · intro hbad
      omega

/-- A nonempty prefix ends at exactly the two hyper-block joints. -/
theorem hyperBlock_prefix_front_joints (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n t : ℕ}
    (Q : FullRungSequence M n) (ht : 1 ≤ t) (htn : t ≤ n)
    (hprefix : ∀ i,1 ≤ i → i ≤ n → (Q.u i ∈ A ↔ i ≤ t))
    (huN : Q.u (n+1) ∉ A) (hvN : Q.v (n+1) ∉ A) :
    ({Q.u t,Q.v t} : Finset V)={a,b} := by
  have hu := (hprefix t ht htn).mpr le_rfl
  have hv := (hyperBlock_sequence_pair_membership M hM hH Q t ht htn).mp hu
  have hun : Q.u (t+1) ∉ A := by
    by_cases he : t=n
    · simpa only [he] using huN
    · intro hh
      have hh' := (hprefix (t+1) (by omega) (by omega)).mp hh
      omega
  have hvn : Q.v (t+1) ∉ A := by
    by_cases he : t=n
    · simpa only [he] using hvN
    · intro hh
      exact hun ((hyperBlock_sequence_pair_membership M hM hH Q (t+1)
        (by omega) (by omega)).mpr hh)
  exact hyperBlock_transition_joints M hM hH (Q.upper t ht htn) (Q.lower t ht htn)
    hu hv (Q.upper_ne_lower ht htn ht htn) (Or.inr hun) (Or.inr hvn)

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperSequenceTransitions
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # A hyper-block cannot occupy a full-rung segment with both ports absent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An arbitrary full-rung sequence with both pairs of external ports
absent has no hyper-block atoms. If a selected interval existed, its first
and last rungs would both have to be the same pair of hyper-block joints,
leaving a single isolated rung of internal degree at most two. -/
theorem hyperBlock_empty_ended_sequence (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n : ℕ}
    (Q : FullRungSequence M n)
    (hu0 : Q.u 0 ∉ A) (hv0 : Q.v 0 ∉ A)
    (huN : Q.u (n+1) ∉ A) (hvN : Q.v (n+1) ∉ A) :
    ∀ i,1 ≤ i → i ≤ n → Q.u i ∉ A ∧ Q.v i ∉ A := by
  intro i hi hin
  have hu : Q.u i ∉ A := by
    intro hxi
    let T := (Icc 1 n).filter (fun j => Q.u j ∈ A)
    have hiT : i ∈ T := mem_filter.mpr ⟨mem_Icc.mpr ⟨hi,hin⟩,hxi⟩
    have hne : T.Nonempty := ⟨i,hiT⟩
    let l := T.min' hne
    let r := T.max' hne
    have hlT : l ∈ T := min'_mem _ hne
    have hrT : r ∈ T := max'_mem _ hne
    have hl := mem_filter.mp hlT
    have hr := mem_filter.mp hrT
    have hlb := mem_Icc.mp hl.1
    have hrb := mem_Icc.mp hr.1
    have hup : Q.u (l-1) ∉ A := by
      by_cases he : l=1
      · simpa only [he] using hu0
      · intro hp
        have hpT : l-1 ∈ T := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hp⟩
        have hh := min'_le T (l-1) hpT
        change l ≤ l-1 at hh
        omega
    have hdn : Q.u (r+1) ∉ A := by
      by_cases he : r=n
      · simpa only [he] using huN
      · intro hp
        have hpT : r+1 ∈ T := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hp⟩
        have hh := le_max' T (r+1) hpT
        change r+1 ≤ r at hh
        omega
    have hvp : Q.v (l-1) ∉ A := by
      by_cases he : l=1
      · simpa only [he] using hv0
      · intro hp
        exact hup ((hyperBlock_sequence_pair_membership M hM hH Q (l-1)
          (by omega) (by omega)).mpr hp)
    have hvn : Q.v (r+1) ∉ A := by
      by_cases he : r=n
      · simpa only [he] using hvN
      · intro hp
        exact hdn ((hyperBlock_sequence_pair_membership M hM hH Q (r+1)
          (by omega) (by omega)).mpr hp)
    have hyl := (hyperBlock_sequence_pair_membership M hM hH Q l hlb.1 hlb.2).mp hl.2
    have hyr := (hyperBlock_sequence_pair_membership M hM hH Q r hrb.1 hrb.2).mp hr.2
    have hlj := hyperBlock_transition_joints M hM hH
      (Q.upper l hlb.1 hlb.2) (Q.lower l hlb.1 hlb.2) hl.2 hyl
      (Q.upper_ne_lower hlb.1 hlb.2 hlb.1 hlb.2) (Or.inl hup) (Or.inl hvp)
    have hrj := hyperBlock_transition_joints M hM hH
      (Q.upper r hrb.1 hrb.2) (Q.lower r hrb.1 hrb.2) hr.2 hyr
      (Q.upper_ne_lower hrb.1 hrb.2 hrb.1 hrb.2) (Or.inr hdn) (Or.inr hvn)
    have he := Q.pair_index_eq hlb.1 hlb.2 hrb.1 hrb.2 (hlj.trans hrj.symm)
    have hnext : Q.u (l+1) ∉ A := by simpa only [he] using hdn
    exact (hyperBlock_rung_not_isolated M hM hH (Q.upper l hlb.1 hlb.2) hl.2).elim hup hnext
  exact ⟨hu,fun hv => hu ((hyperBlock_sequence_pair_membership M hM hH Q i hi hin).mpr hv)⟩

end WaveTurbulence.Vine

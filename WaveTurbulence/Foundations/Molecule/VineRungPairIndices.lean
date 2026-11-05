/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Distinct full-rung indices remain distinguishable as unordered pairs -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- Equality of upper-rail atoms in a full sequence forces equal indices. -/
theorem FullRungSequence.upper_index_eq {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : 1 ≤ j) (hjn : j ≤ n) (he : Q.u i=Q.u j) : i=j := by
  let ii : Fin n := ⟨i-1,by omega⟩
  let jj : Fin n := ⟨j-1,by omega⟩
  have hh : Sum.elim (fun t : Fin n => Q.u (t.1+1)) (fun t : Fin n => Q.v (t.1+1)) (.inl ii)=
      Sum.elim (fun t : Fin n => Q.u (t.1+1)) (fun t : Fin n => Q.v (t.1+1)) (.inl jj) := by
    simpa only [Sum.elim_inl,ii,jj,Nat.sub_add_cancel hi,Nat.sub_add_cancel hj] using he
  have hs := Sum.inl.inj (Q.distinct hh)
  have hv := congrArg Fin.val hs
  dsimp only [ii,jj] at hv
  omega

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- No upper-rail atom equals a lower-rail atom in a full sequence. -/
theorem FullRungSequence.upper_ne_lower {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : 1 ≤ j) (hjn : j ≤ n) : Q.u i ≠ Q.v j := by
  intro he
  let ii : Fin n := ⟨i-1,by omega⟩
  let jj : Fin n := ⟨j-1,by omega⟩
  have hh : Sum.elim (fun t : Fin n => Q.u (t.1+1)) (fun t : Fin n => Q.v (t.1+1)) (.inl ii)=
      Sum.elim (fun t : Fin n => Q.u (t.1+1)) (fun t : Fin n => Q.v (t.1+1)) (.inr jj) := by
    simpa only [Sum.elim_inl,Sum.elim_inr,ii,jj,Nat.sub_add_cancel hi,Nat.sub_add_cancel hj] using he
  have hs := Q.distinct hh
  cases hs

omit [Fintype D] [DecidableEq D] in
/-- An unordered rung pair determines its exact sequence index. -/
theorem FullRungSequence.pair_index_eq {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : 1 ≤ j) (hjn : j ≤ n)
    (he : ({Q.u i,Q.v i} : Finset V)={Q.u j,Q.v j}) : i=j := by
  have hm : Q.u i ∈ ({Q.u j,Q.v j} : Finset V) := he ▸ Finset.mem_insert_self _ _
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with h | h
  · exact Q.upper_index_eq hi hin hj hjn h
  · exact False.elim (Q.upper_ne_lower hi hin hj hjn h)

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
public import WaveTurbulence.Foundations.Molecule.VineRungTransitions
import Mathlib.Tactic

/-! # A non-double connected block has constant membership on a long ladder -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- The two atoms of any recorded full rung are distinct. -/
theorem FullRungSequence.pair_ne {M : Molecule V D} {n : ℕ} (R : FullRungSequence M n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : R.u i ≠ R.v i := by
  intro h
  let idx : Fin n := ⟨i-1,by omega⟩
  have he : Sum.elim (fun j : Fin n => R.u (j.1+1)) (fun j : Fin n => R.v (j.1+1)) (.inl idx) =
      Sum.elim (fun j : Fin n => R.u (j.1+1)) (fun j : Fin n => R.v (j.1+1)) (.inr idx) := by
    simpa only [Sum.elim_inl,Sum.elim_inr,idx,Nat.sub_add_cancel hi] using h
  have hh := R.distinct he
  cases hh

/-- Adjacent full rungs cannot have different membership in a connected
block on more than two atoms. -/
theorem block_adjacent_rungs_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (hcard : 2<S.card) {n : ℕ} (hn : 3 ≤ n) (R : FullRungSequence M n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i+1 ≤ n) : R.u i ∈ S ↔ R.u (i+1) ∈ S := by
  have hcur := block_fullRungSequence_membership M hM hB hn R i hi (by omega)
  have hnext := block_fullRungSequence_membership M hM hB hn R (i+1) (by omega) hin
  have absurd_pair (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (he : S={R.u j,R.v j}) : False := by
    have hc := congrArg Finset.card he
    rw [card_pair (R.pair_ne j hj hjn)] at hc
    omega
  constructor
  · intro hx
    by_contra hxnext
    have hy := hcur.mp hx
    have hynext : R.v (i+1) ∉ S := fun hv => hxnext (hnext.mpr hv)
    have he := block_transition_eq_double_pair M hM hB hC
      (R.upper i hi (by omega)) (R.lower i hi (by omega)) hx hy (R.pair_ne i hi (by omega))
      (Or.inr hxnext) (Or.inr hynext)
    exact absurd_pair i hi (by omega) he
  · intro hxnext
    by_contra hx
    have hynext := hnext.mp hxnext
    have hy : R.v i ∉ S := fun hv => hx (hcur.mpr hv)
    have he := block_transition_eq_double_pair M hM hB hC
      (R.upper (i+1) (by omega) hin) (R.lower (i+1) (by omega) hin)
      hxnext hynext (R.pair_ne (i+1) (by omega) hin)
      (Or.inl (by simpa only [Nat.add_sub_cancel] using hx))
      (Or.inl (by simpa only [Nat.add_sub_cancel] using hy))
    exact absurd_pair (i+1) (by omega) hin he

/-- TARGET subsetvc, ladder reduction: a connected block larger than a double
bond includes either every rung or no rung of any full sequence of length ≥3. -/
theorem block_fullRungSequence_constant (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (hcard : 2<S.card) {n : ℕ} (hn : 3 ≤ n) (R : FullRungSequence M n) :
    ∀ i,1 ≤ i → i ≤ n → ∀ j,1 ≤ j → j ≤ n → (R.u i ∈ S ↔ R.u j ∈ S) := by
  have hlink : ∀ i,1 ≤ i → i ≤ n → (R.u 1 ∈ S ↔ R.u i ∈ S) := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base =>
      intro _h1
      exact Iff.rfl
    | succ i hi ih =>
      intro hin
      exact (ih (by omega)).trans (block_adjacent_rungs_membership M hM hB hC hcard hn R i hi hin)
  intro i hi hin j hj hjn
  exact (hlink i hi hin).symm.trans (hlink j hj hjn)

end WaveTurbulence.Vine

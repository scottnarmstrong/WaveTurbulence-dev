/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineThreeRungIncidences
import Mathlib.Tactic

/-! # Full rung sequences and their three-rung windows (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A sequence of n full rungs, with the two rail endpoints indexed 0 and
n+1. Only the n actual rung pairs enter the injectivity condition. -/
structure FullRungSequence (M : Molecule V D) (n : ℕ) where
  u : ℕ → V
  v : ℕ → V
  distinct : Function.Injective (Sum.elim
    (fun i : Fin n => u (i.1+1)) (fun i : Fin n => v (i.1+1)))
  upper : ∀ i,1 ≤ i → i ≤ n → FourIncidences M (u i) ![v i,v i,u (i-1),u (i+1)]
  lower : ∀ i,1 ≤ i → i ≤ n → FourIncidences M (v i) ![u i,u i,v (i-1),v (i+1)]

/-- Any three successive full rungs form the exact local incidence window. -/
@[expose] def FullRungSequence.window {M : Molecule V D} {n : ℕ}
    (R : FullRungSequence M n) (s : ℕ) (hs : s+3 ≤ n) : ThreeRungIncidences M where
  u := fun i => R.u (s+i)
  v := fun i => R.v (s+i)
  distinct := by
    let e : Fin 6 → Fin n ⊕ Fin n :=
      ![.inl ⟨s,by omega⟩,.inl ⟨s+1,by omega⟩,.inl ⟨s+2,by omega⟩,
        .inr ⟨s,by omega⟩,.inr ⟨s+1,by omega⟩,.inr ⟨s+2,by omega⟩]
    have he : Function.Injective e := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals norm_num [e] at hij
      all_goals norm_num
    have hcomp := R.distinct.comp he
    have heq : ![R.u (s+1),R.u (s+2),R.u (s+3),R.v (s+1),R.v (s+2),R.v (s+3)] =
        (Sum.elim (fun i : Fin n => R.u (i.1+1)) (fun i : Fin n => R.v (i.1+1))) ∘ e := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact hcomp
  d1 := by
    have hh := R.upper (s+1) (by omega) (by omega)
    simpa only [Nat.add_zero,show s+1-1=s by omega,show s+1+1=s+2 by omega] using hh
  d2 := by
    have hh := R.upper (s+2) (by omega) (by omega)
    simpa only [show s+2-1=s+1 by omega,show s+2+1=s+3 by omega] using hh
  d3 := by
    have hh := R.upper (s+3) (by omega) (by omega)
    simpa only [show s+3-1=s+2 by omega,show s+3+1=s+4 by omega] using hh
  e1 := by
    have hh := R.lower (s+1) (by omega) (by omega)
    simpa only [Nat.add_zero,show s+1-1=s by omega,show s+1+1=s+2 by omega] using hh
  e2 := by
    have hh := R.lower (s+2) (by omega) (by omega)
    simpa only [show s+2-1=s+1 by omega,show s+2+1=s+3 by omega] using hh
  e3 := by
    have hh := R.lower (s+3) (by omega) (by omega)
    simpa only [show s+3-1=s+2 by omega,show s+3+1=s+4 by omega] using hh

/-- Every full rung in a sequence of at least three has matched membership
in any block of the ambient molecule, for arbitrary sequence length. -/
theorem block_fullRungSequence_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {n : ℕ} (hn : 3 ≤ n)
    (R : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : R.u i ∈ S ↔ R.v i ∈ S := by
  by_cases hsmall : i ≤ 3
  · have hh := block_three_rungs_membership M hM hB (R.window 0 hn)
    interval_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  · have hs : i-3+3 ≤ n := by omega
    have hh := (block_three_rungs_membership M hM hB (R.window (i-3) hs)).2.2
    change (R.u (i-3+3) ∈ S ↔ R.v (i-3+3) ∈ S) at hh
    simpa only [show i-3+3=i by omega] using hh

end WaveTurbulence.Vine

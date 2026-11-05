/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionNeighbors
import Mathlib.Tactic

/-! # Rail coordinates including the two terminal atoms -/

public section
namespace WaveTurbulence.Vine

/-- Rail coordinates 1,...,k are allocated names, and 0,k+1 are the
old terminal atoms. Values past k+1 stay at the terminal atom. -/
@[expose] def railAtom (n a b k i : ℕ) : ℕ :=
  if i=0 then a else if i ≤ k then n+i-1 else b

/-- Interior coordinates are the freshly allocated rail atoms. -/
theorem railAtom_interior (n a b k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ k) :
    railAtom n a b k i=n+(i-1) := by
  simp only [railAtom,show i ≠ 0 by omega,ite_false,hin,ite_true]
  omega

/-- The predecessor coordinate has the endpoint convention in the fresh
neighbor formula. -/
theorem railAtom_prev (n a b k i : ℕ) (hi : i<k) :
    railAtom n a b k i=if i=0 then a else n+i-1 := by
  by_cases hz : i=0
  · simp only [railAtom,hz,ite_true]
  · simp only [railAtom,hz,ite_false,show i ≤ k by omega,ite_true]

/-- The successor coordinate has the endpoint convention in the fresh
neighbor formula. -/
theorem railAtom_next (n a b k i : ℕ) (hi : i<k) :
    railAtom n a b k (i+2)=if i+1<k then n+i+1 else b := by
  have hzero : i+2 ≠ 0 := by omega
  simp only [railAtom,hzero,ite_false]
  by_cases hh : i+1<k
  · rw [ite_eq_left (by omega),ite_eq_left hh]
    omega
  · rw [ite_eq_right (by omega),ite_eq_right hh]

/-- All coordinates lie below the enclosing allocation bound. -/
theorem railAtom_lt (n a b k i N : ℕ) (ha : a<N) (hb : b<N)
    (halloc : n+k ≤ N) : railAtom n a b k i<N := by
  unfold railAtom
  split_ifs <;> omega

/-- Interior rail coordinates are injective. -/
theorem railAtom_injective (n a b k : ℕ) :
    Function.Injective (fun i : Fin k => railAtom n a b k (i.1+1)) := by
  intro i j hij
  change railAtom n a b k (i.1+1)=railAtom n a b k (j.1+1) at hij
  rw [railAtom_interior n a b k _ (by omega) (by omega),
    railAtom_interior n a b k _ (by omega) (by omega)] at hij
  apply Fin.ext
  omega

end WaveTurbulence.Vine

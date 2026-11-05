/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideBonds
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
import Mathlib.Tactic

/-! # Literal five-edge triangle caps with an arbitrary terminal rung ladder -/

public section
namespace WaveTurbulence.Vine

/-- A rail that stops at its last listed atom and has no further external
bond. Empty lists give no bond. -/
@[expose] def openRailBonds (a : ℕ) (ws : List ℕ) : List (ℕ×ℕ) :=
  List.zip (a::ws) ws

/-- Peel off the first bond of a nonempty open rail. -/
theorem openRailBonds_cons (a w : ℕ) (ws : List ℕ) :
    openRailBonds a (w::ws)=(a,w)::openRailBonds w ws := rfl

/-- An open rail with a specified last atom is the usual closed-end rail. -/
theorem openRailBonds_snoc (a b : ℕ) (ws : List ℕ) :
    openRailBonds a (ws++[b])=railBonds a ws b := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    rw [List.cons_append,openRailBonds_cons,ih,railBonds_cons]

/-- The normal cap triangle, with two doubled sides and one single side. -/
@[expose] def capTriangleBonds : List (ℕ×ℕ) :=
  [(4,5),(4,5),(4,6),(4,6),(5,6)]

/-- A cap with r full terminal rungs. With r=0 its joints are the two
triangle legs; otherwise its joints are the atoms of the last full rung. -/
@[expose] def capBonds (N r : ℕ) : List (ℕ×ℕ) :=
  capTriangleBonds++openRailBonds 5 ((List.range r).map (N+·))++
    openRailBonds 6 ((List.range r).map (N+r+·))++allocatedRungs N (N+r) r

/-- An adjoint cap with k interior full rungs and its final joint pair.
The final rung has one remaining copy after deletion of the added bond. -/
@[expose] def capAdjointBonds (N k : ℕ) : List (ℕ×ℕ) :=
  capTriangleBonds++[(N+k,N+(k+1)+k)]++
    railBonds 5 ((List.range k).map (N+·)) (N+k)++
    railBonds 6 ((List.range k).map (N+(k+1)+·)) (N+(k+1)+k)++
    allocatedRungs N (N+(k+1)) k

/-- Allocated rungs can also be peeled from their last pair. -/
theorem allocatedRungs_snoc (N P k : ℕ) : allocatedRungs N P (k+1)=
    allocatedRungs N P k++[(N+k,P+k),(N+k,P+k)] := by
  simp only [allocatedRungs,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

/-- Positive-length cap normal form, retaining the two final parallel
rung copies separately for the subsequent designated-bond deletion. -/
theorem capBonds_succ (N k : ℕ) : capBonds N (k+1)=
    capTriangleBonds++railBonds 5 ((List.range k).map (N+·)) (N+k)++
      railBonds 6 ((List.range k).map (N+(k+1)+·)) (N+(k+1)+k)++
      allocatedRungs N (N+(k+1)) k++[(N+k,N+(k+1)+k),(N+k,N+(k+1)+k)] := by
  simp only [capBonds,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    openRailBonds_snoc,allocatedRungs_snoc,List.append_assoc]

end WaveTurbulence.Vine

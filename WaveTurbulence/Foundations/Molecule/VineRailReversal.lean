/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-! # Undirected rail lists are invariant under traversal reversal -/

public section
namespace WaveTurbulence.Vine

/-- Forget traversal order and orientations, retaining every parallel bond. -/
@[expose] def rawBondMultiset (es : List (ℕ×ℕ)) : Multiset (Sym2 ℕ) :=
  (es.map (fun p => s(p.1,p.2)) : List (Sym2 ℕ))

/-- Concatenation of raw edges is addition of their bond multisets. -/
theorem rawBondMultiset_append (es fs : List (ℕ×ℕ)) :
    rawBondMultiset (es++fs)=rawBondMultiset es+rawBondMultiset fs := by
  simp [rawBondMultiset]

/-- Peel off the first edge of a rail. -/
theorem railBonds_cons (a w b : ℕ) (ws : List ℕ) :
    railBonds a (w::ws) b=(a,w)::railBonds w ws b := rfl

/-- Peel off the last edge of a rail. -/
theorem railBonds_snoc (a w b : ℕ) (ws : List ℕ) :
    railBonds a (ws++[w]) b=railBonds a ws w++[(w,b)] := by
  induction ws generalizing a with
  | nil => rfl
  | cons v ws ih =>
    change (a,v)::railBonds v (ws++[w]) b=(a,v)::(railBonds v ws w++[(w,b)])
    rw [ih]

/-- Reversing a rail preserves its undirected bond multiset, including the
zero-interior-atom case. -/
theorem rawBondMultiset_rail_reverse (a b : ℕ) (ws : List ℕ) :
    rawBondMultiset (railBonds b ws.reverse a)=rawBondMultiset (railBonds a ws b) := by
  induction ws generalizing a with
  | nil => simp [railBonds,rawBondMultiset,Sym2.eq_swap]
  | cons w ws ih =>
    rw [List.reverse_cons,railBonds_snoc,rawBondMultiset_append,ih,railBonds_cons]
    simp [rawBondMultiset,Sym2.eq_swap,add_comm]

end WaveTurbulence.Vine

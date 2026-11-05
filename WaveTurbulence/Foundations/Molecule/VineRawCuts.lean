/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCutWeights
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Replacing a raw edge by a rail never reduces a cut -/

public section
namespace WaveTurbulence.Vine

/-- Cut size of a literal raw bond list, retaining parallel occurrences. -/
@[expose] def rawCut (W : Finset ℕ) (es : List (ℕ×ℕ)) : ℕ :=
  (es.map (fun p => cutWeight W s(p.1,p.2))).sum

/-- Raw cuts add over concatenated edge lists. -/
theorem rawCut_append (W : Finset ℕ) (es fs : List (ℕ×ℕ)) :
    rawCut W (es++fs)=rawCut W es+rawCut W fs := by simp [rawCut]

/-- A first raw edge contributes its crossing weight. -/
theorem rawCut_cons (W : Finset ℕ) (e : ℕ×ℕ) (es : List (ℕ×ℕ)) :
    rawCut W (e::es)=cutWeight W s(e.1,e.2)+rawCut W es := rfl

/-- Crossing indicators obey the triangle inequality at a third atom. -/
theorem cutWeight_triangle (W : Finset ℕ) (a b c : ℕ) :
    cutWeight W s(a,c) ≤ cutWeight W s(a,b)+cutWeight W s(b,c) := by
  by_cases ha : a ∈ W <;> by_cases hb : b ∈ W <;> by_cases hc : c ∈ W <;>
    simp [cutWeight_pair,ha,hb,hc]

/-- A rail has at least the crossing weight of its two endpoints. -/
theorem rawCut_rail_bound (W : Finset ℕ) (a b : ℕ) (ws : List ℕ) :
    cutWeight W s(a,b) ≤ rawCut W (railBonds a ws b) := by
  induction ws generalizing a with
  | nil => simp [railBonds,rawCut]
  | cons w ws ih =>
    rw [railBonds_cons,rawCut_cons]
    exact (cutWeight_triangle W a w b).trans (Nat.add_le_add_left (ih w) _)

/-- Removing one present occurrence subtracts exactly its crossing weight. -/
theorem rawCut_erase_add (W : Finset ℕ) (es : List (ℕ×ℕ)) (e : ℕ×ℕ) (he : e ∈ es) :
    rawCut W (es.erase e)+cutWeight W s(e.1,e.2)=rawCut W es := by
  have hh := (List.perm_cons_erase he).map (fun p => cutWeight W s(p.1,p.2))
  have hs := hh.sum_eq
  simpa only [rawCut,List.map_cons,List.sum_cons,Nat.add_comm] using hs.symm

/-- Literal rung insertion never decreases a cut on any atom label set.
The new rail endpoints agree with the replaced edges and the added rung
weights are nonnegative. -/
theorem insertRungs_rawCut_le (W : Finset ℕ) (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1) :
    rawCut W T.bonds ≤ rawCut W (insertRungs T s k).bonds := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
  · have he1 := rawCut_erase_add W T.bonds s.1 h1
    have he2 := rawCut_erase_add W (T.bonds.erase s.1) s.2 h2
    have hu := rawCut_rail_bound W s.1.1 s.1.2 ((List.range k).map (T.n+·))
    have hv := rawCut_rail_bound W s.2.1 s.2.2 ((List.range k).map (T.n+k+·))
    simp only [insertRungs,hk,ite_false,rawCut_append]
    omega

end WaveTurbulence.Vine

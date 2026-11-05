/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! # Local block degree recurrence on three successive rungs (TARGET subsetvc)

The 0/1 variables record membership in the nested group. The joint markers
record its two possible degree-two exceptions. Six local degree equations
and the joint budget are data extracted from an actual block, not assumed
membership propagation.
-/

public section
namespace WaveTurbulence.Vine

/-- A three-rung window, with one neighboring atom beyond each end of each
rail. The equation degree+2*jointMarker=4 expresses degree two at joints and
four at all other selected atoms. -/
structure BlockStrip where
  b : ℕ → ℕ
  c : ℕ → ℕ
  j : ℕ → ℕ
  k : ℕ → ℕ
  bBound : ∀ i<5,b i≤1
  cBound : ∀ i<5,c i≤1
  jBound : ∀ i ∈ [1,2,3],j i≤1
  kBound : ∀ i ∈ [1,2,3],k i≤1
  budget : j 1+j 2+j 3+k 1+k 2+k 3≤2
  d1 : b 1=1 → 2*c 1+b 0+b 2+2*j 1=4
  d2 : b 2=1 → 2*c 2+b 1+b 3+2*j 2=4
  d3 : b 3=1 → 2*c 3+b 2+b 4+2*j 3=4
  e1 : c 1=1 → 2*b 1+c 0+c 2+2*k 1=4
  e2 : c 2=1 → 2*b 2+c 1+c 3+2*k 2=4
  e3 : c 3=1 → 2*b 3+c 2+c 4+2*k 3=4

/-- Exchanging the two rails exchanges the joint markers as well. -/
@[expose] def BlockStrip.swap (D : BlockStrip) : BlockStrip where
  b := D.c
  c := D.b
  j := D.k
  k := D.j
  bBound := D.cBound
  cBound := D.bBound
  jBound := D.kBound
  kBound := D.jBound
  budget := by have h := D.budget; omega
  d1 := D.e1
  d2 := D.e2
  d3 := D.e3
  e1 := D.d1
  e2 := D.d2
  e3 := D.d3

private theorem binary_eq_or_split (a b : ℕ) (ha : a≤1) (hb : b≤1) :
    a=b ∨ (a=1 ∧ b=0) ∨ (a=0 ∧ b=1) := by omega

private theorem split_row (l r j : ℕ) (hl : l≤1) (hr : r≤1) (hj : j≤1)
    (he : l+r+2*j=4) : l=1 ∧ r=1 ∧ j=1 := by omega

private theorem neighbor_joint (c q z j k : ℕ) (hc : c≤1) (hq : q≤1) (hz : z≤1)
    (hd : 2*c+1+q+2*j=4)
    (he : c=1 → 2+z+2*k=4) : 1≤j+k := by
  by_cases h : c=1
  · have hh := he h
    omega
  · omega

private theorem middle_split_impossible (D : BlockStrip) (hb : D.b 2=1) (hc : D.c 2=0) : False := by
  have hd := D.d2 hb
  rw [hc] at hd
  have hrow := split_row (D.b 1) (D.b 3) (D.j 2) (D.bBound 1 (by decide))
    (D.bBound 3 (by decide)) (D.jBound 2 (by decide)) (by omega)
  have hleft := neighbor_joint (D.c 1) (D.b 0) (D.c 0) (D.j 1) (D.k 1)
    (D.cBound 1 (by decide)) (D.bBound 0 (by decide)) (D.cBound 0 (by decide))
    (by have h := D.d1 hrow.1; omega)
    (by intro h; have hh := D.e1 h; omega)
  have hright := neighbor_joint (D.c 3) (D.b 4) (D.c 4) (D.j 3) (D.k 3)
    (D.cBound 3 (by decide)) (D.bBound 4 (by decide)) (D.cBound 4 (by decide))
    (by have h := D.d3 hrow.2.1; omega)
    (by intro h; have hh := D.e3 h; omega)
  have hbudget := D.budget
  omega

/-- A split middle rung would require its selected atom and at least one
atom in each neighboring rung to be three distinct joints. -/
theorem middle_rung_equal (D : BlockStrip) : D.b 2=D.c 2 := by
  rcases binary_eq_or_split (D.b 2) (D.c 2) (D.bBound 2 (by decide))
    (D.cBound 2 (by decide)) with h | h | h
  · exact h
  · exact False.elim (middle_split_impossible D h.1 h.2)
  · exact False.elim (middle_split_impossible D.swap h.2 h.1)

end WaveTurbulence.Vine

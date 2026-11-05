/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungRecurrence
import Mathlib.Tactic

/-! # Every rung of a three-rung block window has matched membership -/

public section
namespace WaveTurbulence.Vine

private theorem first_split_impossible (D : BlockStrip) (hb1 : D.b 1=1) (hc1 : D.c 1=0) : False := by
  have hd1 := D.d1 hb1
  have hb0 := D.bBound 0 (by decide)
  have hb2 := D.bBound 2 (by decide)
  have hj1 := D.jBound 1 (by decide)
  rw [hc1] at hd1
  have hr : D.b 2=1 ∧ D.j 1=1 := by omega
  have hc2 : D.c 2=1 := (middle_rung_equal D).symm.trans hr.1
  have hd2 := D.d2 hr.1
  have he2 := D.e2 hc2
  simp only [hb1,hc1,hr.1,hc2] at hd2 he2
  have hb3 := D.bBound 3 (by decide)
  have hc3 := D.cBound 3 (by decide)
  have hj2 := D.jBound 2 (by decide)
  have hk2 := D.kBound 2 (by decide)
  have hbits : D.b 3=1 ∧ D.c 3=0 ∧ D.k 2=1 := by omega
  have hd3 := D.d3 hbits.1
  have hb4 := D.bBound 4 (by decide)
  have hj3 := D.jBound 3 (by decide)
  have hbudget := D.budget
  omega

/-- A split endpoint rung forces one joint there, another in the middle,
and a third at the far rung, contradicting the two-joint budget. -/
theorem first_rung_equal (D : BlockStrip) : D.b 1=D.c 1 := by
  have hb := D.bBound 1 (by decide)
  have hc := D.cBound 1 (by decide)
  by_contra hne
  have hs : (D.b 1=1 ∧ D.c 1=0) ∨ (D.b 1=0 ∧ D.c 1=1) := by omega
  rcases hs with h | h
  · exact first_split_impossible D h.1 h.2
  · exact first_split_impossible D.swap h.2 h.1

/-- Reverse the three-rung window and its two boundary positions. -/
@[expose] def BlockStrip.reverse (D : BlockStrip) : BlockStrip where
  b := fun i => D.b (4-i)
  c := fun i => D.c (4-i)
  j := fun i => D.j (4-i)
  k := fun i => D.k (4-i)
  bBound := by intro i _hi; apply D.bBound; omega
  cBound := by intro i _hi; apply D.cBound; omega
  jBound := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact D.jBound 3 (by decide)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact D.jBound 2 (by decide)
      · have he : i=3 := List.mem_singleton.mp hi
        subst i
        exact D.jBound 1 (by decide)
  kBound := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact D.kBound 3 (by decide)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact D.kBound 2 (by decide)
      · have he : i=3 := List.mem_singleton.mp hi
        subst i
        exact D.kBound 1 (by decide)
  budget := by have h := D.budget; change D.j 3+D.j 2+D.j 1+D.k 3+D.k 2+D.k 1≤2; omega
  d1 := by intro h; have hh := D.d3 h; norm_num only [Nat.reduceSub]; omega
  d2 := by intro h; have hh := D.d2 h; norm_num only [Nat.reduceSub]; omega
  d3 := by intro h; have hh := D.d1 h; norm_num only [Nat.reduceSub]; omega
  e1 := by intro h; have hh := D.e3 h; norm_num only [Nat.reduceSub]; omega
  e2 := by intro h; have hh := D.e2 h; norm_num only [Nat.reduceSub]; omega
  e3 := by intro h; have hh := D.e1 h; norm_num only [Nat.reduceSub]; omega

/-- The far endpoint rung has matched membership by rail reversal. -/
theorem third_rung_equal (D : BlockStrip) : D.b 3=D.c 3 := first_rung_equal D.reverse

/-- Any three-rung block window has identical membership along each rung. -/
theorem three_rungs_equal (D : BlockStrip) :
    D.b 1=D.c 1 ∧ D.b 2=D.c 2 ∧ D.b 3=D.c 3 :=
  ⟨first_rung_equal D,middle_rung_equal D,third_rung_equal D⟩

end WaveTurbulence.Vine

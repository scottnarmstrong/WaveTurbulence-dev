/-
Copyright (c) 2026 Jason Hickey, Scott Armstrong. All rights reserved.
Released under Apache 2.0 license; see ../NumberTheory/SALT-LICENSE.
Authors: Jason Hickey, Claude, Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Interval fibers of monotone sequences

A non-strict version of the interval-fiber argument used by the discrete
second-derivative test. Adapted from Jason Hickey's
`Salt/ExpSum/VdCorput2.lean`, commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
This is for the exact integer block decomposition in NT-CIRCLE-v2 goal 2.
-/

public section

namespace WaveTurbulence.Counting

/-- The inverse image of a half-open interval under a monotone sequence,
restricted to a finite natural interval, is another natural interval. -/
theorem filter_monotone_Ioc_lt_le_eq_Ioc {g : ℕ → ℝ} {a b : ℕ}
    (hmono : MonotoneOn g (Set.Ioc a b)) (u v : ℝ) :
    ∃ a' b' : ℕ, a ≤ a' ∧ b' ≤ b ∧
      (Finset.Ioc a b).filter (fun n => u < g n ∧ g n ≤ v) = Finset.Ioc a' b' := by
  classical
  let T := (Finset.Ioc a b).filter (fun n => u < g n ∧ g n ≤ v)
  rcases T.eq_empty_or_nonempty with he | hne
  · refine ⟨a, 0, le_rfl, Nat.zero_le b, ?_⟩
    rw [← show T = (Finset.Ioc a b).filter (fun n => u < g n ∧ g n ≤ v) from rfl, he]
    exact (Finset.Ioc_eq_empty (by omega)).symm
  · let n0 := T.min' hne
    let n1 := T.max' hne
    have hn0 := Finset.mem_filter.mp (T.min'_mem hne)
    have hn1 := Finset.mem_filter.mp (T.max'_mem hne)
    have ha0 : a < n0 := (Finset.mem_Ioc.mp hn0.1).1
    have hb1 : n1 ≤ b := (Finset.mem_Ioc.mp hn1.1).2
    refine ⟨n0 - 1, n1, by omega, hb1, ?_⟩
    ext x
    constructor
    · intro hx
      have hx0 : n0 ≤ x := T.min'_le x hx
      have hx1 : x ≤ n1 := T.le_max' x hx
      exact Finset.mem_Ioc.mpr ⟨by omega, hx1⟩
    · intro hx
      obtain ⟨hx0, hx1⟩ := Finset.mem_Ioc.mp hx
      have hxa : a < x := by omega
      have hxb : x ≤ b := hx1.trans hb1
      have hx0' : n0 ≤ x := by omega
      have hxmem : x ∈ Set.Ioc a b := ⟨hxa, hxb⟩
      have hg0 := hmono (Finset.mem_Ioc.mp hn0.1) hxmem hx0'
      have hg1 := hmono hxmem (Finset.mem_Ioc.mp hn1.1) hx1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hxmem,
        hn0.2.1.trans_le hg0, hg1.trans hn1.2.2⟩

end WaveTurbulence.Counting

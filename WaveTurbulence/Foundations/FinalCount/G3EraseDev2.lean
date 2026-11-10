/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
/-! **FINALCOUNT-G3: the flux dichotomy of an erasure** (R27, research-remtame-i L1, L2).

`sgnC C` is the net signed number of bonds from `v` into the component `C` of `M - v`.  `Pinned M v`: some component meeting `v`
has `sgnC ≠ 0`.  If `deg v = 3` then `v` is pinned; if `deg v = 4` then `v` is pinned or at most two components of `M - v` meet
`v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V)

/-- The darts of `C` whose bond goes to `v`. -/
noncomputable def crossD (C : Finset V) : Finset D := Finset.univ.filter (fun x => M.atom x ∈ C ∧ M.atom (M.mate x) = v)

variable {M v}

theorem dartSign_cases (x : D) : M.dartSign x = 1 ∨ M.dartSign x = -1 := by
  unfold Molecule.dartSign; split_ifs <;> simp

theorem dartSign_mate (x : D) : M.dartSign (M.mate x) = - M.dartSign x := by
  unfold Molecule.dartSign
  have := M.out_mate x
  cases h : M.out x <;> cases h2 : M.out (M.mate x) <;> simp_all

theorem sum_dartSign_dartsAt (a : V) :
    ∑ y ∈ M.dartsAt a, M.dartSign y = (M.outdeg a : ℝ) - M.indeg a := by
  unfold Molecule.outdeg Molecule.indeg
  have h := Finset.sum_filter_add_sum_filter_not (M.dartsAt a) (fun x => M.out x = true) (fun y => M.dartSign y)
  have e1 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.out x = true), M.dartSign x =
      (((M.dartsAt a).filter fun x => M.out x = true).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    simp [Molecule.dartSign, this]
  have e2 : ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.out x = true), M.dartSign x =
      -(((M.dartsAt a).filter fun x => M.out x = false).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    have hf : (M.dartsAt a).filter (fun x => M.out x = false) = (M.dartsAt a).filter (fun x => ¬ M.out x = true) := by
      ext x; simp
    rw [hf]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    simp [Molecule.dartSign, this]
  rw [← h, e1, e2]; ring

end WaveTurbulence.FinalCountG3

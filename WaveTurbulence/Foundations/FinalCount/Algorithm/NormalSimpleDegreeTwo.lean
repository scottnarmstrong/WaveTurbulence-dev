/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoChange
import Mathlib.Tactic

/-! # Normal S33, D33 and R3 preserve the actual V2-star statistic -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Local predicate cancellation, with only old and new vertex degrees as
premises. Source normal operations below derive those degrees from the table. -/
theorem simpleDegreeTwo_count_eq_of_local_degrees {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P)
    (hpre : ∀ a ∈ P.vertices,M.deg (r.vertex a) ≠ 2)
    (hpost : ∀ a ∈ P.vertices,a ∉ P.removed → r.post.deg (r.vertex a) ≠ 2) :
    (simpleDegreeTwoAtoms r.post).card = (simpleDegreeTwoAtoms M).card := by
  classical
  have hh := SimpleStarChange.difference r
  have hz : (∑ a ∈ P.vertices,
      ((if a ∉ P.removed ∧ SimpleDegreeTwo r.post (r.vertex a) then (1 : ℤ) else 0)-
        (if SimpleDegreeTwo M (r.vertex a) then 1 else 0))) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hnpre : ¬SimpleDegreeTwo M (r.vertex a) := fun h => hpre a ha h.1
    have hnpost : ¬(a ∉ P.removed ∧ SimpleDegreeTwo r.post (r.vertex a)) :=
      fun h => hpost a ha h.1 h.2.1
    simp only [hnpre,hnpost,ite_false,sub_self]
  rw [hz] at hh
  omega

/-- DH23's V2-star preservation in the normal S33, D33 and R3 cases.
Every displayed survivor has old degree four; the removed degree-three
atoms and the one-incidence survivor decrements follow from the figures. -/
theorem normal_simpleDegreeTwo_unchanged (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.s33,.d33,.r3] : List _))
    (r : AppbRealization M k.pattern)
    (hb : ∀ a ∈ k.pattern.vertices,a ∉ k.pattern.removed → M.deg (r.vertex a) = 4) :
    (simpleDegreeTwoAtoms r.post).card = (simpleDegreeTwoAtoms M).card := by
  have ht : ∀ k ∈ ([AppbPatternKind.s33,.d33,.r3] : List _),
      ∀ a ∈ k.pattern.vertices,
        (a ∈ k.pattern.removed → k.pattern.localDegree a = 3) ∧
        (a ∉ k.pattern.removed → k.pattern.localDegree a = 1) := by decide
  apply simpleDegreeTwo_count_eq_of_local_degrees r
  · intro a ha
    by_cases hr : a ∈ k.pattern.removed
    · have hh := r.deleted_degree a hr
      rw [(ht k hk a ha).1 hr] at hh
      omega
    · rw [hb a ha hr]
      decide
  · intro a ha hr
    have hh := r.post_vertex_degree a ha
    rw [hb a ha hr,(ht k hk a ha).2 hr] at hh
    omega

end WaveTurbulence.Mole.AppbAlgorithm

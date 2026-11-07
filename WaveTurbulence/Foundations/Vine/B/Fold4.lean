/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold3
import Mathlib.Tactic

/-!
# VINE-B Part I (4): the splice boundary of a unit is its crown

For a (CL) block `u` of `G`, the three boundary roots of the actual splice (`clSpliceBoundary`, whichever slot data
`D` is used) are exactly the three crown nodes `u11, u21, u22` of `crownSet u`, and the realization of `u` is the
set of nodes below the upper joint and not below a boundary root.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

theorem slots_unique {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (D D' : CLSpliceSlots G S a b) :
    D.excluded = D'.excluded ∧ D.kept = D'.kept := by
  constructor
  · have h1 := D.upper D'.excluded
    have h2 := D'.upper D'.excluded
    have : ¬ (D'.excluded ≠ D.excluded) := fun h => by
      have := h2.mpr
      exact (h1.mpr h) |> fun hm => (h2.mp hm) rfl
    exact (not_not.mp this).symm
  · have h1 := D.lower D'.kept
    have h2 := D'.lower D'.kept
    exact (h1.mp (h2.mpr rfl)).symm

theorem fin3_cases_ne (k p : Fin 3) (hk : k ≠ 1) (hp : p ≠ k) : p = 1 ∨ p = otherOuterChild k := by
  fin_cases k <;> fin_cases p <;> simp_all [otherOuterChild]

variable (u : CLBlock G) (D : CLSpliceSlots G u.atoms u.upper u.lower)

theorem bnode_def (i : Fin 3) :
    (clSpliceBoundary u.isBlock u.cl D).node i =
      (![u.upper.child D.excluded, u.lower.child 1, u.lower.child (otherOuterChild D.kept)] : Fin 3 → GNode G.tree)
        (clBoundarySelector D.excluded (clSameSign u.upper u.lower) i) := rfl

theorem crownSet_iff_bnode (x : GNode G.tree) :
    x ∈ crownSet u ↔ ∃ i, (clSpliceBoundary u.isBlock u.cl D).node i = x := by
  have hu := (slots_unique D (regionOf u).toCLSpliceSlots)
  have hk1 := D.kept_ne_middle
  have hbij := clBoundarySelector_bijective D.excluded D.excluded_ne_middle (clSameSign u.upper u.lower)
  have hlo := (regionOf u).lower_excluded
  have hke : (regionOf u).kept = D.kept := hu.2.symm
  have hee : (regionOf u).excluded = D.excluded := hu.1.symm
  constructor
  · rintro (h | h | h)
    · obtain ⟨i, hi⟩ := hbij.2 0
      refine ⟨i, ?_⟩
      rw [bnode_def, hi, h, hee]; rfl
    · have hp : (regionOf u).positive ≠ D.kept := by
        rw [← hke]; exact fun he => ((hlo _).mpr (Or.inl rfl)) he
      rcases fin3_cases_ne _ _ hk1 hp with h1 | h1
      · obtain ⟨i, hi⟩ := hbij.2 1
        refine ⟨i, ?_⟩
        rw [bnode_def, hi, h, h1]; rfl
      · obtain ⟨i, hi⟩ := hbij.2 2
        refine ⟨i, ?_⟩
        rw [bnode_def, hi, h, h1]; rfl
    · have hp : (regionOf u).negative ≠ D.kept := by
        rw [← hke]; exact fun he => ((hlo _).mpr (Or.inr rfl)) he
      rcases fin3_cases_ne _ _ hk1 hp with h1 | h1
      · obtain ⟨i, hi⟩ := hbij.2 1
        refine ⟨i, ?_⟩
        rw [bnode_def, hi, h, h1]; rfl
      · obtain ⟨i, hi⟩ := hbij.2 2
        refine ⟨i, ?_⟩
        rw [bnode_def, hi, h, h1]; rfl
  · rintro ⟨i, rfl⟩
    rw [bnode_def]
    generalize clBoundarySelector D.excluded (clSameSign u.upper u.lower) i = j
    fin_cases j
    · left; simp [hee]
    · right
      have : (1 : Fin 3) ≠ (regionOf u).kept := by rw [hke]; exact hk1.symm
      rcases (hlo 1).mp this with h | h
      · left; exact congrArg u.lower.child h
      · right; exact congrArg u.lower.child h
    · right
      have : otherOuterChild D.kept ≠ (regionOf u).kept := by
        rw [hke]; exact otherOuterChild_ne _ hk1
      rcases (hlo _).mp this with h | h
      · left; exact congrArg u.lower.child h
      · right; exact congrArg u.lower.child h

theorem real_iff_bnode (z : GNode G.tree) :
    z ∈ clRealizationNodes G u.atoms ↔
      u.upper.toNode.IsDesc z ∧ ¬ ∃ i, ((clSpliceBoundary u.isBlock u.cl D).node i).IsDesc z := by
  rw [real_iff]
  have key : (∃ i, ((clSpliceBoundary u.isBlock u.cl D).node i).IsDesc z) ↔
      ((u.upper.child (regionOf u).excluded).IsDesc z ∨ (u.lower.child (regionOf u).positive).IsDesc z ∨
        (u.lower.child (regionOf u).negative).IsDesc z) := by
    constructor
    · rintro ⟨i, hi⟩
      have : (clSpliceBoundary u.isBlock u.cl D).node i ∈ crownSet u := (crownSet_iff_bnode u D _).mpr ⟨i, rfl⟩
      rcases this with h | h | h
      · left; rw [← h]; exact hi
      · right; left; rw [← h]; exact hi
      · right; right; rw [← h]; exact hi
    · rintro (h | h | h)
      · obtain ⟨i, hi⟩ := (crownSet_iff_bnode u D (u.upper.child (regionOf u).excluded)).mp (Or.inl rfl)
        exact ⟨i, by rw [hi]; exact h⟩
      · obtain ⟨i, hi⟩ := (crownSet_iff_bnode u D (u.lower.child (regionOf u).positive)).mp (Or.inr (Or.inl rfl))
        exact ⟨i, by rw [hi]; exact h⟩
      · obtain ⟨i, hi⟩ := (crownSet_iff_bnode u D (u.lower.child (regionOf u).negative)).mp (Or.inr (Or.inr rfl))
        exact ⟨i, by rw [hi]; exact h⟩
  rw [key]
  tauto

end WaveTurbulence.VineB

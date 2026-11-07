/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairStars
import Mathlib.Tactic

/-! # The stars of a `(4,4)` double pair -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Stars of a `(4,4)` double pair**: `x, y` are the two bonds `v₁ → v₂`, `r₁, r₂` the other darts at `v₁`,
`s₁, s₂` the other darts at `v₂`. -/
theorem stars44 (M : Molecule V D) {v₁ v₂ : V} (hne : v₁ ≠ v₂) (h1 : M.deg v₁ = 4) (h2 : M.deg v₂ = 4)
    (hbb : M.bondsBetween v₁ v₂ = 2) :
    ∃ x y r₁ r₂ s₁ s₂ : D, x ≠ y ∧ x ≠ r₁ ∧ x ≠ r₂ ∧ y ≠ r₁ ∧ y ≠ r₂ ∧ r₁ ≠ r₂ ∧
      M.mate x ≠ M.mate y ∧ M.mate x ≠ s₁ ∧ M.mate x ≠ s₂ ∧ M.mate y ≠ s₁ ∧ M.mate y ≠ s₂ ∧ s₁ ≠ s₂ ∧
      M.atom x = v₁ ∧ M.atom (M.mate x) = v₂ ∧ M.atom y = v₁ ∧ M.atom (M.mate y) = v₂ ∧
      M.dartsAt v₁ = {x, y, r₁, r₂} ∧ M.dartsAt v₂ = {M.mate x, M.mate y, s₁, s₂} ∧
      (∀ z, M.ends z = s(v₁, v₂) → z = x ∨ z = y ∨ z = M.mate x ∨ z = M.mate y) := by
  classical
  obtain ⟨x, y, hxy, hxy'⟩ := card_eq_two.mp ((card_darts_between M hne).trans hbb)
  have hxm : x ∈ univ.filter fun z => M.atom z = v₁ ∧ M.atom (M.mate z) = v₂ := by rw [hxy']; simp
  have hym : y ∈ univ.filter fun z => M.atom z = v₁ ∧ M.atom (M.mate z) = v₂ := by rw [hxy']; simp
  obtain ⟨_, hxa, hxb⟩ := mem_filter.mp hxm
  obtain ⟨_, hya, hyb⟩ := mem_filter.mp hym
  have hmxy : M.mate x ≠ M.mate y := fun h => hxy (by simpa [M.mate_mate] using congrArg M.mate h)
  have hsubA : ({x, y} : Finset D) ⊆ M.dartsAt v₁ := by
    intro z hz; rw [Mole.mem_dartsAt]
    rcases mem_insert.mp hz with rfl | hz
    · exact hxa
    · rw [mem_singleton.mp hz]; exact hya
  obtain ⟨r₁, hr₁, hr₁xy⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hxy]; unfold Molecule.deg at h1; omega : ({x, y} : Finset D).card < (M.dartsAt v₁).card)
  have hxr₁ : x ≠ r₁ := fun h => hr₁xy (by rw [← h]; simp)
  have hyr₁ : y ≠ r₁ := fun h => hr₁xy (by rw [← h]; simp)
  obtain ⟨r₂, hr₂, hr₂xy⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_insert_of_notMem (by simp [hxr₁.symm, hyr₁.symm] : r₁ ∉ ({x, y} : Finset D)), card_pair hxy]
    unfold Molecule.deg at h1; omega : ({r₁, x, y} : Finset D).card < (M.dartsAt v₁).card)
  have hxr₂ : x ≠ r₂ := fun h => hr₂xy (by rw [← h]; simp)
  have hyr₂ : y ≠ r₂ := fun h => hr₂xy (by rw [← h]; simp)
  have hrr : r₁ ≠ r₂ := fun h => hr₂xy (by rw [← h]; simp)
  have hA : M.dartsAt v₁ = {x, y, r₁, r₂} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at h1
      rw [h1]
      have : ({x, y, r₁, r₂} : Finset D) = insert x (insert y (insert r₁ {r₂})) := rfl
      rw [this, card_insert_of_notMem (by simp [hxy, hxr₁, hxr₂]), card_insert_of_notMem (by simp [hyr₁, hyr₂]),
        card_pair hrr])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hsubA (by simp)
    · exact hsubA (by simp)
    · exact hr₁
    · exact hr₂
  have hsubB : ({M.mate x, M.mate y} : Finset D) ⊆ M.dartsAt v₂ := by
    intro z hz; rw [Mole.mem_dartsAt]
    rcases mem_insert.mp hz with rfl | hz
    · exact hxb
    · rw [mem_singleton.mp hz]; exact hyb
  obtain ⟨s₁, hs₁, hs₁x⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hmxy]; unfold Molecule.deg at h2; omega : ({M.mate x, M.mate y} : Finset D).card < (M.dartsAt v₂).card)
  have hms1x : M.mate x ≠ s₁ := fun h => hs₁x (by rw [← h]; simp)
  have hms1y : M.mate y ≠ s₁ := fun h => hs₁x (by rw [← h]; simp)
  obtain ⟨s₂, hs₂, hs₂x⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_insert_of_notMem (by simp [hms1x.symm, hms1y.symm] : s₁ ∉ ({M.mate x, M.mate y} : Finset D)), card_pair hmxy]
    unfold Molecule.deg at h2; omega : ({s₁, M.mate x, M.mate y} : Finset D).card < (M.dartsAt v₂).card)
  have hms2x : M.mate x ≠ s₂ := fun h => hs₂x (by rw [← h]; simp)
  have hms2y : M.mate y ≠ s₂ := fun h => hs₂x (by rw [← h]; simp)
  have hss : s₁ ≠ s₂ := fun h => hs₂x (by rw [← h]; simp)
  have hB : M.dartsAt v₂ = {M.mate x, M.mate y, s₁, s₂} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at h2
      rw [h2]
      have : ({M.mate x, M.mate y, s₁, s₂} : Finset D) =
          insert (M.mate x) (insert (M.mate y) (insert s₁ {s₂})) := rfl
      rw [this, card_insert_of_notMem (by simp [hmxy, hms1x, hms2x]), card_insert_of_notMem (by simp [hms1y, hms2y]),
        card_pair hss])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hsubB (by simp)
    · exact hsubB (by simp)
    · exact hs₁
    · exact hs₂
  have hpair : ∀ z, M.ends z = s(v₁, v₂) → z = x ∨ z = y ∨ z = M.mate x ∨ z = M.mate y := by
    intro z hz
    have hz' : s(M.atom z, M.atom (M.mate z)) = s(v₁, v₂) := hz
    rcases Sym2.eq_iff.mp hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : z ∈ univ.filter fun w => M.atom w = v₁ ∧ M.atom (M.mate w) = v₂ := mem_filter.mpr ⟨mem_univ _, h1, h2⟩
      rw [hxy'] at this
      rcases mem_insert.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (mem_singleton.mp h))
    · have : M.mate z ∈ univ.filter fun w => M.atom w = v₁ ∧ M.atom (M.mate w) = v₂ :=
        mem_filter.mpr ⟨mem_univ _, h2, by rw [M.mate_mate]; exact h1⟩
      rw [hxy'] at this
      rcases mem_insert.mp this with h | h
      · exact Or.inr (Or.inr (Or.inl (by rw [← h, M.mate_mate])))
      · exact Or.inr (Or.inr (Or.inr (by rw [← mem_singleton.mp h, M.mate_mate])))
  exact ⟨x, y, r₁, r₂, s₁, s₂, hxy, hxr₁, hxr₂, hyr₁, hyr₂, hrr, hmxy, hms1x, hms2x, hms1y, hms2y, hss,
    hxa, hxb, hya, hyb, hA, hB, hpair⟩

end WaveTurbulence.FinalCountG8

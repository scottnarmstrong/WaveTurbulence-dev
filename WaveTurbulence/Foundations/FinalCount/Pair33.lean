/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairStars
public import WaveTurbulence.Foundations.CountLemmas.A23HalfReparam
import Mathlib.Tactic

/-! # The five-label count for a `(3,3)` single pair (DH23 Lemma A.3(4), `{(1,2,3),(1,4,5)}`, `γ > 1/2`)

Atoms `a, b` of degree three joined by one bond `m`; the other bonds `e₂, e₃` of `a` and `f₄, f₅` of `b`. The five labels
solve the conservation law and energy window at `a` (tuple `(m, e₂, e₃)`) and at `b` (tuple `(m, f₄, f₅)`), i.e. the
system `{(1,2,3),(1,4,5)}` of A23-HALF's `system12345_bound`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Stars of a `(3,3)` single pair.** -/
theorem stars33 (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (hbb : M.bondsBetween a b = 1) :
    ∃ m e2 e3 f4 f5 : D, m ≠ e2 ∧ m ≠ e3 ∧ e2 ≠ e3 ∧ M.mate m ≠ f4 ∧ M.mate m ≠ f5 ∧ f4 ≠ f5 ∧
      M.atom m = a ∧ M.atom (M.mate m) = b ∧ M.dartsAt a = {m, e2, e3} ∧ M.dartsAt b = {M.mate m, f4, f5} := by
  classical
  obtain ⟨m, hm⟩ := card_eq_one.mp ((card_darts_between M hab).trans hbb)
  have hmm : m ∈ univ.filter fun z => M.atom z = a ∧ M.atom (M.mate z) = b := by rw [hm]; simp
  obtain ⟨_, hma, hmb⟩ := mem_filter.mp hmm
  have hsubA : ({m} : Finset D) ⊆ M.dartsAt a := by
    intro z hz; rw [Mole.mem_dartsAt]; rw [mem_singleton.mp hz]; exact hma
  obtain ⟨e2, he2, he2m⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [Finset.card_singleton]; unfold Molecule.deg at hda; omega : ({m} : Finset D).card < (M.dartsAt a).card)
  have hme2 : m ≠ e2 := fun h => he2m (by rw [← h]; simp)
  obtain ⟨e3, he3, he3m⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hme2]; unfold Molecule.deg at hda; omega : ({m, e2} : Finset D).card < (M.dartsAt a).card)
  have hme3 : m ≠ e3 := fun h => he3m (by rw [← h]; simp)
  have he23 : e2 ≠ e3 := fun h => he3m (by rw [← h]; simp)
  have hA : M.dartsAt a = {m, e2, e3} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at hda
      rw [hda, card_insert_of_notMem (by simp [hme2, hme3]), card_pair he23])
    rcases mem_insert.mp hz with rfl | hz
    · exact hsubA (by simp)
    · rcases mem_insert.mp hz with rfl | hz
      · exact he2
      · rw [mem_singleton.mp hz]; exact he3
  have hsubB : ({M.mate m} : Finset D) ⊆ M.dartsAt b := by
    intro z hz; rw [Mole.mem_dartsAt]; rw [mem_singleton.mp hz]; exact hmb
  obtain ⟨f4, hf4, hf4m⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [Finset.card_singleton]; unfold Molecule.deg at hdb; omega : ({M.mate m} : Finset D).card < (M.dartsAt b).card)
  have hmf4 : M.mate m ≠ f4 := fun h => hf4m (by rw [← h]; simp)
  obtain ⟨f5, hf5, hf5m⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hmf4]; unfold Molecule.deg at hdb; omega : ({M.mate m, f4} : Finset D).card < (M.dartsAt b).card)
  have hmf5 : M.mate m ≠ f5 := fun h => hf5m (by rw [← h]; simp)
  have hf45 : f4 ≠ f5 := fun h => hf5m (by rw [← h]; simp)
  have hB : M.dartsAt b = {M.mate m, f4, f5} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at hdb
      rw [hdb, card_insert_of_notMem (by simp [hmf4, hmf5]), card_pair hf45])
    rcases mem_insert.mp hz with rfl | hz
    · exact hsubB (by simp)
    · rcases mem_insert.mp hz with rfl | hz
      · exact hf4
      · rw [mem_singleton.mp hz]; exact hf5
  exact ⟨m, e2, e3, f4, f5, hme2, hme3, he23, hmf4, hmf5, hf45, hma, hmb, hA, hB⟩

end WaveTurbulence.FinalCountG8

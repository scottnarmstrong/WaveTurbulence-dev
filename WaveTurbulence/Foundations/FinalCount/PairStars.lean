/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseI
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveDeletion
import Mathlib.Tactic

/-! # The local star structure of a `(3,4)` double pair

G6's `exists_double_pair_stars` derives the stars of an adjacent pair `a, b` (`a` of degree 3, `b` of degree 4, two bonds
between them) from a ladder cell. The stars themselves only need the degrees and the molecule caps; this module
proves them without a cell (`stars34`), so that G6's five-label count applies to any such pair (`PairGainAt`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem outdeg_triple' (M : Molecule V D) (a : V) {x y z : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hstar : M.dartsAt a = {x,y,z}) :
    M.outdeg a = (if M.out x = true then 1 else 0) + (if M.out y = true then 1 else 0) +
      (if M.out z = true then 1 else 0) := by
  have hh := sum_dartsAt_triple M a hxy hxz hyz hstar (fun q => if M.out q = true then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.outdeg,Nat.cast_id] using hh

theorem indeg_triple' (M : Molecule V D) (a : V) {x y z : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hstar : M.dartsAt a = {x,y,z}) :
    M.indeg a = (if M.out x = false then 1 else 0) + (if M.out y = false then 1 else 0) +
      (if M.out z = false then 1 else 0) := by
  have hh := sum_dartsAt_triple M a hxy hxz hyz hstar (fun q => if M.out q = false then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.indeg,Nat.cast_id] using hh

theorem outdeg_quad' (M : Molecule V D) (a : V) {x y z t : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht : t ∉ ({x,y,z} : Finset D))
    (hstar : M.dartsAt a = {x,y,z,t}) :
    M.outdeg a = (if M.out x = true then 1 else 0) + (if M.out y = true then 1 else 0) +
      (if M.out z = true then 1 else 0) + (if M.out t = true then 1 else 0) := by
  have hh := sum_dartsAt_quadruple M a hxy hxz hyz ht hstar (fun q => if M.out q = true then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.outdeg,Nat.cast_id] using hh

theorem indeg_quad' (M : Molecule V D) (a : V) {x y z t : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht : t ∉ ({x,y,z} : Finset D))
    (hstar : M.dartsAt a = {x,y,z,t}) :
    M.indeg a = (if M.out x = false then 1 else 0) + (if M.out y = false then 1 else 0) +
      (if M.out z = false then 1 else 0) + (if M.out t = false then 1 else 0) := by
  have hh := sum_dartsAt_quadruple M a hxy hxz hyz ht hstar (fun q => if M.out q = false then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.indeg,Nat.cast_id] using hh

/-- **Stars of a `(3,4)` double pair.** -/
theorem stars34 (M : Molecule V D) (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (hbb : M.bondsBetween a b = 2) :
    ∃ x y r s t : D, x ≠ y ∧ x ≠ r ∧ y ≠ r ∧ M.mate x ≠ M.mate y ∧ M.mate x ≠ s ∧ M.mate y ≠ s ∧
      t ∉ ({M.mate x, M.mate y, s} : Finset D) ∧ M.dartsAt a = {x, y, r} ∧
      M.dartsAt b = {M.mate x, M.mate y, s, t} ∧ M.out s = !M.out r := by
  classical
  obtain ⟨x, y, hxy, hxy'⟩ := card_eq_two.mp ((card_darts_between M hab).trans hbb)
  have hxm : x ∈ univ.filter fun z => M.atom z = a ∧ M.atom (M.mate z) = b := by rw [hxy']; simp
  have hym : y ∈ univ.filter fun z => M.atom z = a ∧ M.atom (M.mate z) = b := by rw [hxy']; simp
  obtain ⟨_, hxa, hxb⟩ := mem_filter.mp hxm
  obtain ⟨_, hya, hyb⟩ := mem_filter.mp hym
  have hmxy : M.mate x ≠ M.mate y := fun h => hxy (by simpa [M.mate_mate] using congrArg M.mate h)
  -- the star at `a`
  have hsubA : ({x, y} : Finset D) ⊆ M.dartsAt a := by
    intro z hz; rw [Mole.mem_dartsAt]
    rcases mem_insert.mp hz with rfl | hz
    · exact hxa
    · rw [mem_singleton.mp hz]; exact hya
  obtain ⟨r, hrA, hrxy⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hxy]; unfold Molecule.deg at hda; omega : ({x, y} : Finset D).card < (M.dartsAt a).card)
  have hxr : x ≠ r := fun h => hrxy (by rw [← h]; simp)
  have hyr : y ≠ r := fun h => hrxy (by rw [← h]; simp)
  have hAstar : M.dartsAt a = {x, y, r} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at hda
      rw [hda, card_insert_of_notMem (by simp [hxy, hxr]), card_pair hyr])
    rcases mem_insert.mp hz with rfl | hz
    · exact hsubA (by simp)
    · rcases mem_insert.mp hz with rfl | hz
      · exact hsubA (by simp)
      · rw [mem_singleton.mp hz]; exact hrA
  -- the star at `b`
  have hsubB : ({M.mate x, M.mate y} : Finset D) ⊆ M.dartsAt b := by
    intro z hz; rw [Mole.mem_dartsAt]
    rcases mem_insert.mp hz with rfl | hz
    · exact hxb
    · rw [mem_singleton.mp hz]; exact hyb
  obtain ⟨u, huB, hu⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_pair hmxy]; unfold Molecule.deg at hdb; omega : ({M.mate x, M.mate y} : Finset D).card < (M.dartsAt b).card)
  have hu1 : M.mate x ≠ u := fun h => hu (by rw [← h]; simp)
  have hu2 : M.mate y ≠ u := fun h => hu (by rw [← h]; simp)
  obtain ⟨v, hvB, hv⟩ := exists_mem_notMem_of_card_lt_card (by
    rw [card_insert_of_notMem (by simp [hu1.symm, hu2.symm] : u ∉ ({M.mate x, M.mate y} : Finset D)), card_pair hmxy]
    unfold Molecule.deg at hdb; omega : ({u, M.mate x, M.mate y} : Finset D).card < (M.dartsAt b).card)
  have hv1 : M.mate x ≠ v := fun h => hv (by rw [← h]; simp)
  have hv2 : M.mate y ≠ v := fun h => hv (by rw [← h]; simp)
  have huv : u ≠ v := fun h => hv (by rw [← h]; simp)
  have hBstar : M.dartsAt b = {M.mate x, M.mate y, u, v} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      unfold Molecule.deg at hdb
      rw [hdb]
      have : ({M.mate x, M.mate y, u, v} : Finset D) = insert (M.mate x) (insert (M.mate y) (insert u {v})) := rfl
      rw [this, card_insert_of_notMem (by simp [hmxy, hu1, hv1]), card_insert_of_notMem (by simp [hu2, hv2]),
        card_pair huv])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hsubB (by simp)
    · exact hsubB (by simp)
    · exact huB
    · exact hvB
  -- orientations
  have hcapA := hcap a ha
  have hcapB := hcap b hb
  have hsumB := Mole.outdeg_add_indeg M b
  rw [outdeg_triple' M a hxy hxr hyr hAstar] at hcapA
  rw [indeg_triple' M a hxy hxr hyr hAstar] at hcapA
  have hnt' : v ∉ ({M.mate x, M.mate y, u} : Finset D) := by simp [hv1.symm, hv2.symm, huv.symm]
  have hout := outdeg_quad' M b hmxy hu1 hu2 hnt' hBstar
  have hin := indeg_quad' M b hmxy hu1 hu2 hnt' hBstar
  rw [M.out_mate, M.out_mate] at hout hin
  have hdeg4 : M.outdeg b + M.indeg b = 4 := by rw [hsumB]; unfold Molecule.deg at hdb; exact hdb
  have hv_or : M.out u = !M.out r ∨ M.out v = !M.out r := by
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := hno
    have hu' : M.out u = M.out r := by cases hu : M.out u <;> cases hr : M.out r <;> simp_all
    have hv' : M.out v = M.out r := by cases hv : M.out v <;> cases hr : M.out r <;> simp_all
    rw [hu', hv'] at hout hin
    cases hx : M.out x <;> cases hy : M.out y <;> cases hr : M.out r <;> simp_all
  have hBstar' : M.dartsAt b = {M.mate x, M.mate y, v, u} := by
    rw [hBstar, Finset.pair_comm u v]
  have hnt2 : u ∉ ({M.mate x, M.mate y, v} : Finset D) := by simp [hu1.symm, hu2.symm, huv]
  rcases hv_or with h | h
  · exact ⟨x, y, r, u, v, hxy, hxr, hyr, hmxy, hu1, hu2, hnt', hAstar, hBstar, h⟩
  · exact ⟨x, y, r, v, u, hxy, hxr, hyr, hmxy, hv1, hv2, hnt2, hAstar, hBstar', h⟩

end WaveTurbulence.FinalCountG8

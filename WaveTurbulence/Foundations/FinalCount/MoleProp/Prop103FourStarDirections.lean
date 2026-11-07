/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Actual direction caps on the two remaining bonds of a four-star -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two distinct actual incidences at a degree-four atom extend to its
complete actual four-star, without an orientation premise. -/
theorem exists_remaining_pair_of_degree_four (M : Molecule V D) {v : V} {x y : D}
    (hv4 : M.deg v = 4) (hx : M.atom x = v) (hy : M.atom y = v) (hxy : x ≠ y) :
    ∃ r s : D, M.atom r = v ∧ M.atom s = v ∧ x ≠ r ∧ x ≠ s ∧ y ≠ r ∧ y ≠ s ∧ r ≠ s ∧
      M.dartsAt v = {x,y,r,s} := by
  classical
  have hsub : {x,y} ⊆ M.dartsAt v := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M v x).mpr hx,(Mole.mem_dartsAt M v y).mpr hy⟩
  have hc : ((M.dartsAt v) \ {x,y}).card = 2 := by
    have hh := card_sdiff_add_card_eq_card hsub
    rw [card_pair hxy] at hh
    change (M.dartsAt v).card = 4 at hv4
    omega
  obtain ⟨r,s,hrs,hDiff⟩ := card_eq_two.mp hc
  have hr : r ∈ (M.dartsAt v) \ {x,y} := by rw [hDiff]; simp
  have hs : s ∈ (M.dartsAt v) \ {x,y} := by rw [hDiff]; simp
  have hr' := mem_sdiff.mp hr
  have hs' := mem_sdiff.mp hs
  have hxr : x ≠ r := fun h => hr'.2 (by simp [← h])
  have hxs : x ≠ s := fun h => hs'.2 (by simp [← h])
  have hyr : y ≠ r := fun h => hr'.2 (by simp [← h])
  have hys : y ≠ s := fun h => hs'.2 (by simp [← h])
  refine ⟨r,s,(Mole.mem_dartsAt M v r).mp hr'.1,(Mole.mem_dartsAt M v s).mp hs'.1,
    hxr,hxs,hyr,hys,hrs,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M v x).mpr hx,(Mole.mem_dartsAt M v y).mpr hy,hr'.1,hs'.1⟩
  · change M.deg v ≤ _
    simp [hv4,hxy,hxr,hxs,hyr,hys,hrs]

/-- If two bonds of an actual four-star have the same direction, the
remaining two both point the other way. This is the source easy-positive
pair branch, derived solely from the actual molecule caps. -/
theorem remaining_out_of_four_star_pair_eq (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} (hv : v ∈ M.atoms) {x y r s : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hxs : x ≠ s)
    (hyr : y ≠ r) (hys : y ≠ s) (hrs : r ≠ s)
    (hstar : M.dartsAt v = {x,y,r,s}) (hOut : M.out x = M.out y) :
    M.out r = ! M.out x ∧ M.out s = ! M.out x := by
  have ho := (hM.1 v hv).1
  have hi := (hM.1 v hv).2
  change ((M.dartsAt v).filter (fun z => M.out z = true)).card ≤ 2 at ho
  change ((M.dartsAt v).filter (fun z => M.out z = false)).card ≤ 2 at hi
  rw [hstar] at ho hi
  cases hxO : M.out x <;> cases hrO : M.out r <;> cases hsO : M.out s
  all_goals
    have hyO := hOut.symm.trans hxO
    simp [filter_insert,filter_singleton,hxy,hxr,hxs,hyr,hys,hrs,hxO,hyO,hrO,hsO] at ho hi ⊢

end WaveTurbulence.MoleProp

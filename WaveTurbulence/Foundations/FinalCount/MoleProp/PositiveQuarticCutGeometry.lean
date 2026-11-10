/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.QuarticPositiveProfile
import Mathlib.Tactic

/-! # Actual old-cut data determining quartic labels on first-star profiles

The predicate is purely graph theoretic: a label is already a first-star
bond, or an old cut has just that bond and first-star bonds on its boundary.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def FirstProfileCut (M : Molecule V D) (x y z p : D) : Prop :=
  p ∈ ({x,y,z,M.mate x,M.mate y,M.mate z} : Finset D) ∨
    ∃ U : Finset V, U ⊆ M.atoms ∧ M.mate p ∈ Degen.boundaryDarts M U ∧
      Degen.boundaryDarts M U ⊆ {M.mate p,M.mate x,M.mate y,M.mate z}

theorem firstProfileCut_mate_first (M : Molecule V D) (x y z : D) :
    FirstProfileCut M x y z (M.mate x) := by
  left
  simp

theorem firstProfileCut_label_unique (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {x y z p r s : D} (hcut : FirstProfileCut M x y z p)
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (hp : sharedFirstProfile (doubleFiveProfile x y z r s κ)=
      sharedFirstProfile (doubleFiveProfile x y z r s κ')) : κ p=κ' p := by
  have hx : κ x=κ' x := congrFun hp 0
  have hy : κ y=κ' y := congrFun hp 1
  have hz : κ z=κ' z := congrFun hp 2
  rcases hcut with hp | ⟨U,hU,he,hsub⟩
  · simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
    · simpa only [hd.1,hd'.1] using hx
    · simpa only [hd.1,hd'.1] using hy
    · simpa only [hd.1,hd'.1] using hz
  · have hh : κ (M.mate p)=κ' (M.mate p) := by
      apply cut_label_unique_of_other_labels M hL hd hd' U hU (M.mate p) he
      intro w hw hne
      have hw' := hsub hw
      simp only [mem_insert,mem_singleton] at hw'
      rcases hw' with hw' | rfl | rfl | rfl
      · exact (hne hw').elim
      · simpa only [hd.1,hd'.1] using hx
      · simpa only [hd.1,hd'.1] using hy
      · simpa only [hd.1,hd'.1] using hz
    simpa only [hd.1,hd'.1] using hh

theorem positive_quartic_deletedLabels_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} {p q x y z r s : D}
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {p,q,r,s})
    (hp : FirstProfileCut M x y z p) (hq : FirstProfileCut M x y z q)
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (he : doubleFiveProfile x y z r s κ=doubleFiveProfile x y z r s κ') :
    deletedLabels M {a,b} κ=deletedLabels M {a,b} κ' := by
  have hx : κ x=κ' x := congrFun he 0
  have hy : κ y=κ' y := congrFun he 1
  have hz : κ z=κ' z := congrFun he 2
  have hr : κ r=κ' r := congrFun he 3
  have hs : κ s=κ' s := congrFun he 4
  have hefirst := congrArg sharedFirstProfile he
  have hep := firstProfileCut_label_unique M hL hp hd hd' hefirst
  have heq := firstProfileCut_label_unique M hL hq hd hd' hefirst
  have hAt : ∀ w : D, M.atom w ∈ ({a,b} : Finset V) → κ w=κ' w := by
    intro w hw
    rcases mem_insert.mp hw with hwa | hwb
    · have hw' := (Mole.mem_dartsAt M a w).mpr hwa
      rw [hA] at hw'
      simp only [mem_insert,mem_singleton] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    · have hw' := (Mole.mem_dartsAt M b w).mpr (mem_singleton.mp hwb)
      rw [hB] at hw'
      simp only [mem_insert,mem_singleton] at hw'
      rcases hw' with rfl | rfl | rfl | rfl
      · exact hep
      · exact heq
      · exact hr
      · exact hs
  funext w
  change κ w.val=κ' w.val
  by_cases hw : M.atom w.val ∈ ({a,b} : Finset V)
  · exact hAt w.val hw
  · have hmate : M.atom (M.mate w.val) ∈ ({a,b} : Finset V) := by
      by_contra hh
      exact w.property ⟨hw,hh⟩
    simpa only [hd.1,hd'.1] using hAt (M.mate w.val) hmate

end WaveTurbulence.MoleProp

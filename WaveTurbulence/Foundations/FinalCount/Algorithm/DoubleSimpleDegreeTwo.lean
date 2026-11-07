/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoChange
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # Double degree-two groups and their actual V2-star effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem not_simpleDegreeTwo_of_double (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hd : M.deg a = 2) (hm : M.bondsBetween a b = 2) : ¬SimpleDegreeTwo M a := by
  classical
  intro hs
  obtain ⟨_,c,hc,d,hd',hac,had,hcd,hmc,hmd⟩ := hs
  have hA : (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) = M.dartsAt a := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    rw [← bondsBetween_eq_card_darts M hab,hm]
    exact hd.le
  have hcp : 0 < ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = c)).card := by
    rw [← bondsBetween_eq_card_darts M hac,hmc]
    decide
  obtain ⟨x,hx⟩ := card_pos.mp hcp
  obtain ⟨hx,hxc⟩ := mem_filter.mp hx
  have hxb : M.atom (M.mate x) = b := by
    have hxB : x ∈ (M.dartsAt a).filter (fun z => M.atom (M.mate z) = b) := by
      rw [hA]; exact hx
    exact (mem_filter.mp hxB).2
  have hcb : c = b := hxc.symm.trans hxb
  rw [hcb,hm] at hmc
  omega

/-- DH23 2R-1F cannot decrease V2-star. Its removed double-bond atom
was not simple, and its degree-four neighbor was not simple either. -/
theorem r21_simpleDegreeTwo_nondecrease (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r21.pattern)
    (h2 : M.deg (r.vertex 2) = 4) :
    (simpleDegreeTwoAtoms M).card ≤ (simpleDegreeTwoAtoms r.post).card := by
  classical
  have hn12 : r.vertex 1 ≠ r.vertex 2 :=
    (r.vertex_eq_iff 1 2 (by decide) (by decide)).not.mpr (by decide)
  have hdeg : M.deg (r.vertex 1) = 2 := r.deleted_degree 1 (by decide)
  have hmult : M.bondsBetween (r.vertex 1) (r.vertex 2) = 2 :=
    (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)
  have hn1 := not_simpleDegreeTwo_of_double M hn12 hdeg hmult
  have hn2 : ¬SimpleDegreeTwo M (r.vertex 2) := fun h => by have hh := h.1; omega
  have hn : ∀ a ∈ AppbPatternKind.r21.pattern.vertices,¬SimpleDegreeTwo M (r.vertex a) := by
    intro a ha
    have hV : AppbPatternKind.r21.pattern.vertices = {1,2} := by decide
    rw [hV] at ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hn1
    · have he : a = 2 := mem_singleton.mp ha
      subst a
      exact hn2
  have hh := SimpleStarChange.difference r
  have hnon : (0 : ℤ) ≤ ∑ a ∈ AppbPatternKind.r21.pattern.vertices,
      ((if a ∉ AppbPatternKind.r21.pattern.removed ∧ SimpleDegreeTwo r.post (r.vertex a) then (1 : ℤ) else 0)-
        (if SimpleDegreeTwo M (r.vertex a) then 1 else 0)) := by
    apply sum_nonneg
    intro a ha
    simp only [hn a ha,ite_false,sub_zero]
    split_ifs <;> omega
  omega

/-- DH23 2R-4F deletes a closed double pair; neither old atom was V2-star. -/
theorem r24_simpleDegreeTwo_unchanged (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r24.pattern) :
    (simpleDegreeTwoAtoms r.post).card = (simpleDegreeTwoAtoms M).card := by
  classical
  have hne : r.vertex 1 ≠ r.vertex 2 :=
    (r.vertex_eq_iff 1 2 (by decide) (by decide)).not.mpr (by decide)
  have h1 : M.deg (r.vertex 1) = 2 := r.deleted_degree 1 (by decide)
  have h2 : M.deg (r.vertex 2) = 2 := r.deleted_degree 2 (by decide)
  have hm : M.bondsBetween (r.vertex 1) (r.vertex 2) = 2 :=
    (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)
  have hm' : M.bondsBetween (r.vertex 2) (r.vertex 1) = 2 := (bondsBetween_symm M _ _).trans hm
  have hn1 := not_simpleDegreeTwo_of_double M hne h1 hm
  have hn2 := not_simpleDegreeTwo_of_double M hne.symm h2 hm'
  have hh := SimpleStarChange.difference r
  have hV : AppbPatternKind.r24.pattern.vertices = {1,2} := by decide
  rw [hV,sum_pair (by decide)] at hh
  simp [AppbPatternKind.pattern,hn1,hn2] at hh
  exact_mod_cast (sub_eq_zero.mp hh)

end WaveTurbulence.Mole.AppbAlgorithm

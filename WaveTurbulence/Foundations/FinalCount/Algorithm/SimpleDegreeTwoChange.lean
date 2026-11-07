/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeThreeChangeBound
import Mathlib.Tactic

/-! # Exact local V2-star sum and its bounded change under literal deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SimpleStarChange
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

open Classical in
theorem difference :
    ((simpleDegreeTwoAtoms r.post).card : ℤ)-(simpleDegreeTwoAtoms M).card =
      ∑ a ∈ P.vertices,
        ((if a ∉ P.removed ∧ SimpleDegreeTwo r.post (r.vertex a) then (1 : ℤ) else 0)-
          (if SimpleDegreeTwo M (r.vertex a) then 1 else 0)) := by
  classical
  let f : V → ℤ := fun v =>
    (if v ∉ r.removedAtoms ∧ SimpleDegreeTwo r.post v then 1 else 0)-
      (if SimpleDegreeTwo M v then 1 else 0)
  have hp : ((simpleDegreeTwoAtoms r.post).card : ℤ) =
      ∑ v ∈ M.atoms,if v ∉ r.removedAtoms ∧ SimpleDegreeTwo r.post v then (1 : ℤ) else 0 := by
    have he : simpleDegreeTwoAtoms r.post = M.atoms.filter
        (fun v => v ∉ r.removedAtoms ∧ SimpleDegreeTwo r.post v) := by
      ext v
      simp only [simpleDegreeTwoAtoms,mem_filter]
      change ((v ∈ M.atoms \ r.removedAtoms) ∧ _) ↔ _
      simp only [mem_sdiff]
      tauto
    rw [he,sum_boole]
  have hm : ((simpleDegreeTwoAtoms M).card : ℤ) =
      ∑ v ∈ M.atoms,if SimpleDegreeTwo M v then (1 : ℤ) else 0 := (sum_boole _ _).symm
  rw [hp,hm,← sum_sub_distrib]
  change (∑ v ∈ M.atoms,f v) = _
  have hsub : P.vertices.image r.vertex ⊆ M.atoms := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    exact r.vertex_mem a ha
  have hs : (∑ v ∈ M.atoms,f v) = ∑ v ∈ P.vertices.image r.vertex,f v := by
    symm
    apply sum_subset hsub
    intro v hv hout
    have hnot : v ∉ r.removedAtoms := by
      intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact hout (mem_image_of_mem _ (mem_union_left _ ha))
    have he := AppbRealization.simpleDegreeTwo_iff_outside r hout
    simp only [f,hnot,not_false_eq_true,true_and,he,sub_self]
  rw [hs,sum_image]
  · apply sum_congr rfl
    intro a ha
    simp only [f,r.vertex_mem_removed_iff a ha]
  · exact r.vertex_injective

theorem abs_difference_le :
    |((simpleDegreeTwoAtoms r.post).card : ℤ)-(simpleDegreeTwoAtoms M).card| ≤ P.vertices.card := by
  classical
  rw [difference r]
  exact sum_indicator_difference_abs_le P.vertices _ _

end SimpleStarChange
end WaveTurbulence.Mole.AppbAlgorithm

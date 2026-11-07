/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
import Mathlib.Tactic

/-! # Exact degree-count changes under the Appendix B operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TableDegree
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Full local formula for any degree-count change. It preserves arbitrary ambient
boundary degrees, and counts every unaffected atom by cancellation. -/
theorem post_degreeCount_difference (k : ℕ) :
    ((appbDegreeAtoms r.post k).card : ℤ) - (appbDegreeAtoms M k).card =
      ∑ a ∈ P.vertices,
        ((if a ∉ P.removed ∧ M.deg (r.vertex a) = k + P.localDegree a then (1 : ℤ) else 0) -
          (if M.deg (r.vertex a) = k then 1 else 0)) := by
  classical
  let f : V → ℤ := fun v =>
    (if v ∉ r.removedAtoms ∧ r.post.deg v = k then 1 else 0) -
    (if M.deg v = k then 1 else 0)
  have hpost : ((appbDegreeAtoms r.post k).card : ℤ) =
      ∑ v ∈ M.atoms, if v ∉ r.removedAtoms ∧ r.post.deg v = k then (1 : ℤ) else 0 := by
    have he : appbDegreeAtoms r.post k =
        M.atoms.filter (fun v => v ∉ r.removedAtoms ∧ r.post.deg v = k) := by
      ext v
      simp only [appbDegreeAtoms,mem_filter]
      change (v ∈ M.atoms \ r.removedAtoms ∧ r.post.deg v = k) ↔ _
      simp only [mem_sdiff]
      tauto
    rw [he,sum_boole]

  have hpre : ((appbDegreeAtoms M k).card : ℤ) =
      ∑ v ∈ M.atoms, if M.deg v = k then (1 : ℤ) else 0 := (sum_boole _ _).symm
  rw [hpost,hpre,← sum_sub_distrib]
  change (∑ v ∈ M.atoms, f v) = _
  have hsub : P.vertices.image r.vertex ⊆ M.atoms := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    exact r.vertex_mem a ha
  have hs : (∑ v ∈ M.atoms, f v) = ∑ v ∈ P.vertices.image r.vertex, f v := by
    symm
    apply sum_subset hsub
    intro v hv hout
    have hd := r.post_degree_outside v hout
    have hnot : v ∉ r.removedAtoms := by
      intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact hout (mem_image_of_mem _ (mem_union_left _ ha))
    simp [f,hnot,hd]
  rw [hs,sum_image]
  · apply sum_congr rfl
    intro a ha
    have hm := r.vertex_mem_removed_iff a ha
    have hd := r.post_vertex_degree a ha
    have he : r.post.deg (r.vertex a) = k ↔ M.deg (r.vertex a) = k + P.localDegree a := by omega
    simp only [f,hm,he]
  · intro a ha b hb he
    exact r.vertex_injective ha hb he

end TableDegree
end WaveTurbulence.Mole.AppbAlgorithm

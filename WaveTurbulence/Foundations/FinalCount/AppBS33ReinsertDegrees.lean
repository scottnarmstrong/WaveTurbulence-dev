/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # The four displayed survivor degrees in 3S3-3G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_reinsert_survivor_degree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (j : ℕ) (hj : j ∈ ({3,4,5,6} : Finset ℕ)) :
    (r.directedPostWithBond 3 5 ⟨1,by decide⟩).deg (r.vertex j) +
      (if j = 3 ∨ j = 5 then 0 else 1) = M.deg (r.vertex j) := by
  have hjV : j ∈ AppbPatternKind.s33.pattern.vertices := by
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have hpost : r.post.deg (r.vertex j)+1 = M.deg (r.vertex j) := by
    have hh := r.post_vertex_degree j hjV
    have hn : AppbPatternKind.s33.pattern.localDegree j = 1 := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    simpa only [hn] using hh
  have h3 : r.vertex 3 = r.vertex j ↔ 3 = j := r.vertex_eq_iff 3 j (by decide) hjV
  have h5 : r.vertex 5 = r.vertex j ↔ 5 = j := r.vertex_eq_iff 5 j (by decide) hjV
  unfold AppbRealization.directedPostWithBond
  split_ifs
  all_goals rw [r.postWithBond_degree]
  all_goals simp only [h3,h5]
  all_goals split_ifs <;> omega

end WaveTurbulence.Mole

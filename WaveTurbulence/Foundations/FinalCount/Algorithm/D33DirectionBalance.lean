/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SignedRealization
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33Continuation
import Mathlib.Tactic

/-! # Degree-four orientation balance forces the next rung's opposite rails -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_boundary_signed_sum_zero (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r) :
    (∑ x ∈ r.post.dartsAt (r.vertex 3),r.post.dartSign x)+
      (∑ x ∈ r.post.dartsAt (r.vertex 4),r.post.dartSign x) = 0 := by
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hz3 := sum_dartSign_zero_of_degree_four M hM (r.vertex_mem 3 (by decide)) h3
  have hz4 := sum_dartSign_zero_of_degree_four M hM (r.vertex_mem 4 (by decide)) h4
  have hr3 := sum_removed_sign_single_incidence r 3 (by decide) hn3 (2 : Fin 4) (by
    intro i; fin_cases i <;> decide)
  have hr4 := sum_removed_sign_single_incidence r 4 (by decide) hn4 (3 : Fin 4) (by
    intro i; fin_cases i <;> decide)
  have hs3 : (∑ x ∈ M.dartsAt (r.vertex 3),M.dartSign x) =
      (∑ x ∈ r.post.dartsAt (r.vertex 3),r.post.dartSign x)+
        ∑ x ∈ Degen.removedDartsAt M r.removedAtoms (r.vertex 3),M.dartSign x :=
    Degen.sum_dartsAt_split M r.removedAtoms hn3 M.dartSign
  have hs4 : (∑ x ∈ M.dartsAt (r.vertex 4),M.dartSign x) =
      (∑ x ∈ r.post.dartsAt (r.vertex 4),r.post.dartSign x)+
        ∑ x ∈ Degen.removedDartsAt M r.removedAtoms (r.vertex 4),M.dartSign x :=
    Degen.sum_dartsAt_split M r.removedAtoms hn4 M.dartSign
  have hopp : AppbOppositeFrom M (r.vertex 3) (r.vertex 4)
      (r.edge (2 : Fin 4)).val (r.edge (3 : Fin 4)).val :=
    (appb_incidence_sign_opposite_from M _ _ _ _).mp (appb_d33_external_signs_opposite r ho)
  have he := (edgeSign_sum_zero_iff M _ _ _ _).mpr hopp
  linarith only [hz3,hz4,hr3,hr4,hs3,hs4,he]

/-- The extra opposite-rail condition in the source continuation test is
a consequence of the actual degree caps and the preceding opposite rails.
It is not an additional assumption about the next figure. -/
theorem d33_next_boundary_opposite (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r)
    (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4) :
    AppbD33BoundaryOpposite r.post t := by
  have hz := d33_boundary_signed_sum_zero M hM r h3 h4 ho
  have hs := d33_head_signed_sum r.post t
  apply (edgeSign_sum_zero_iff r.post (t.vertex 1) (t.vertex 2)
    (t.edge (2 : Fin 4)).val (t.edge (3 : Fin 4)).val).mp
  rw [h1,h2] at hs ⊢
  linarith only [hz,hs]

end WaveTurbulence.Mole.AppbAlgorithm

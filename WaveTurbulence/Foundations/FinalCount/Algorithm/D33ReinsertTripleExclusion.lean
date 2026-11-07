/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33DoubleContinuation
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TripleSelection
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertDegrees
import Mathlib.Tactic

/-! # The source algorithm excludes a newly formed degree-four triple pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_reinsert_boundary_multiplicity (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) :
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).bondsBetween (r.vertex 3) (r.vertex 4) =
      M.bondsBetween (r.vertex 3) (r.vertex 4)+1 := by
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hm : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = M.bondsBetween (r.vertex 3) (r.vertex 4) :=
    Degen.bondsBetween_erase_eq M r.removedAtoms hn3 hn4
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · change (addBond r.post (r.vertex 3) (r.vertex 4)).bondsBetween _ _ = _
    rw [appb_addBond_bondsBetween,if_pos rfl,hm]
  · change (addBond r.post (r.vertex 4) (r.vertex 3)).bondsBetween _ _ = _
    rw [appb_addBond_bondsBetween,if_pos (Sym2.eq_swap),hm]

/-- DH23 algorithm remark two: a triple between two degree-four boundary
atoms would force precisely the continuation/common-tail alternative that
was excluded before selecting 3D3-3G. -/
theorem d33_reinsert_triple_not_both_four (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r)
    (hm : (r.directedPostWithBond 3 4 ⟨2,by decide⟩).bondsBetween (r.vertex 3) (r.vertex 4) = 3) :
    ¬((r.directedPostWithBond 3 4 ⟨2,by decide⟩).deg (r.vertex 3) = 4 ∧
      (r.directedPostWithBond 3 4 ⟨2,by decide⟩).deg (r.vertex 4) = 4) := by
  rintro ⟨h3,h4⟩
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hd3 : M.deg (r.vertex 3) = 4 := (appb_d33_reinsert_degree M r hn3).symm.trans h3
  have hd4 : M.deg (r.vertex 4) = 4 := (appb_d33_reinsert_degree M r hn4).symm.trans h4
  have hmult := d33_reinsert_boundary_multiplicity M r
  have hold : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by omega
  exact d33_terminal_boundary_not_double M hM hno r hd3 hd4 ho hc ht hold

end WaveTurbulence.Mole.AppbAlgorithm

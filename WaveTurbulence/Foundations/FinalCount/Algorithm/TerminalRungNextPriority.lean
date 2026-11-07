/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33TerminalPairExclusion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33BoundaryRegular
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GraphPriorities
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Actual progress after the source terminal normal rung

The scan remains in the current connected component. Its two surviving
boundary atoms have degree three, and there is no degree-three double
pair. Thus the next priority cannot restart a primary double-rung chain.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem terminal_rung_next_priority (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (hconn : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r)
    (hreg : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4) :
    r.post.bonds.Nonempty ∧ ¬HasDegreeThreePair r.post 2 ∧ GraphPriority r.post := by
  classical
  have hdeg := d33_terminal_boundary_four r hreg
  have hd3 := hdeg 3 (by decide) (by decide)
  have hd4 := hdeg 4 (by decide) (by decide)
  have he3 := r.post_vertex_degree 3 (by decide)
  have hn3 : AppbPatternKind.d33.pattern.localDegree 3 = 1 := by decide
  rw [hd3,hn3] at he3
  have hp3 : r.post.deg (r.vertex 3) = 3 := by omega
  have hnon : r.post.bonds.Nonempty := by
    by_contra hn
    have hempty := not_nonempty_iff_eq_empty.mp hn
    have hsum := sum_degrees_eq_two_mul_bonds r.post
    have hle : r.post.deg (r.vertex 3) ≤ ∑ a ∈ r.post.atoms,r.post.deg a :=
      single_le_sum (fun a _ => Nat.zero_le _) (r.vertex_mem_post 3 (by decide) (by decide))
    rw [hempty,card_empty,mul_zero] at hsum
    omega
  have hnot : ¬HasDegreeThreePair r.post 2 := by
    rintro ⟨a,ha,b,hb,hda,hdb,hab,hm⟩
    exact d33_terminal_no_degree_three_double_in_component M hM hno r hd3 hd4 ho hc ht hreg ha hb
      (hconn _ (r.vertex_mem 1 (by decide)) _ (mem_sdiff.mp ha).1) hda hdb hab hm
  exact ⟨hnon,hnot,exists_graph_priority r.post
    (appb_eraseAtoms_isMolecule M hM r.removedAtoms)
    (appb_eraseAtoms_noLoops M r.removedAtoms hno)
    (appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt) hnon⟩

end WaveTurbulence.Mole.AppbAlgorithm

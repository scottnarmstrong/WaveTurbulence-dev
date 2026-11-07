/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairDoubleClassification
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairSharedClassification
import Mathlib.Tactic

/-! # Exhaustive single-bonded degree-three pair classification in rule two -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SinglePairEdges
variable {M : Molecule V D} {a b : V}

theorem figure (data : SinglePairEdges M a b)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) : SinglePairFigure M := by
  classical
  by_cases hl : data.left.neighbor 0 = data.left.neighbor 1
  · exact data.figure_of_left_double ha hb hab hda hdb hl
  by_cases hr : data.right.neighbor 0 = data.right.neighbor 1
  · exact data.swap.figure_of_left_double hb ha hab.symm hdb hda hr
  by_cases h00 : data.left.neighbor 0 = data.right.neighbor 0
  · exact data.figure_of_shared_boundary ha hb hab hda hdb hl hr h00
  by_cases h01 : data.left.neighbor 0 = data.right.neighbor 1
  · apply (data.reindex (Equiv.refl _) (Equiv.swap 0 1)).figure_of_shared_boundary ha hb hab hda hdb
    · simpa [reindex] using hl
    · simpa [reindex] using (Ne.symm hr)
    · simpa [reindex] using h01
  by_cases h10 : data.left.neighbor 1 = data.right.neighbor 0
  · apply (data.reindex (Equiv.swap 0 1) (Equiv.refl _)).figure_of_shared_boundary ha hb hab hda hdb
    · simpa [reindex] using (Ne.symm hl)
    · simpa [reindex] using hr
    · simpa [reindex] using h10
  by_cases h11 : data.left.neighbor 1 = data.right.neighbor 1
  · apply (data.reindex (Equiv.swap 0 1) (Equiv.swap 0 1)).figure_of_shared_boundary ha hb hab hda hdb
    · simpa [reindex] using (Ne.symm hl)
    · simpa [reindex] using (Ne.symm hr)
    · simpa [reindex] using h11
  let c := data.left.neighbor 0
  let d := data.left.neighbor 1
  let p := data.right.neighbor 0
  let q := data.right.neighbor 1
  have hc : c ∈ M.atoms := data.left.neighbor_mem 0
  have hd : d ∈ M.atoms := data.left.neighbor_mem 1
  have hp : p ∈ M.atoms := data.right.neighbor_mem 0
  have hq : q ∈ M.atoms := data.right.neighbor_mem 1
  have hca : c ≠ a := data.left.neighbor_ne_center 0
  have hcb : c ≠ b := data.left.neighbor_ne_partner 0
  have hda' : d ≠ a := data.left.neighbor_ne_center 1
  have hdb' : d ≠ b := data.left.neighbor_ne_partner 1
  have hpa : p ≠ a := data.right.neighbor_ne_partner 0
  have hpb : p ≠ b := data.right.neighbor_ne_center 0
  have hqa : q ≠ a := data.right.neighbor_ne_partner 1
  have hqb : q ≠ b := data.right.neighbor_ne_center 1
  have hcd : c ≠ d := hl
  have hpq : p ≠ q := hr
  have hcp : c ≠ p := h00
  have hcq : c ≠ q := h01
  have hdp : d ≠ p := h10
  have hdq : d ≠ q := h11
  have hnd : ([a,b,c,d,p,q] : List V).Nodup := by simp_all [ne_comm]
  have hm : ∀ v ∈ ([a,b,c,d,p,q] : List V),v ∈ M.atoms := by
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  let r := s33Realization M hab hnd hm hda hdb data rfl rfl rfl rfl
  exact ⟨.s33,by simp,⟨r⟩⟩

end SinglePairEdges

/-- DH23 Appendix B rule two's assertion that its seven figures exhaust
a pair of degree-three atoms joined by exactly one bond. -/
theorem exists_single_pair_figure (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (hm : M.bondsBetween a b = 1) :
    SinglePairFigure M :=
  (singlePairEdges M hno hda hdb hm).figure ha hb hab hda hdb

end WaveTurbulence.Mole.AppbAlgorithm

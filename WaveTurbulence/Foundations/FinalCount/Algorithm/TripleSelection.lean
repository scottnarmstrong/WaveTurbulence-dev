/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TriplePatterns
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Source TB selection from an actual triple and the degree-four exclusion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

inductive TripleSelection (M : Molecule V D) : Prop
  | closed (r : AppbRealization M AppbPatternKind.tb1.pattern) : TripleSelection M
  | tail (r : AppbRealization M AppbPatternKind.tb2.pattern) : TripleSelection M

theorem bondsBetween_le_degree (M : Molecule V D) {a b : V} (hab : a ≠ b) :
    M.bondsBetween a b ≤ M.deg a := by
  rw [bondsBetween_eq_card_darts M hab]
  exact Finset.card_filter_le _ _

theorem triple_selection_of_degree_three (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3 ∨ M.deg b = 4)
    (hm : M.bondsBetween a b = 3) : TripleSelection M := by
  classical
  rcases hdb with hdb | hdb
  · have hnd : ([a,b] : List V).Nodup := by simp [hab]
    have hmem : ∀ v ∈ ([a,b] : List V),v ∈ M.atoms := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl <;> assumption
    let data : MixedPairEdges M a b 3 0 0 := mixedPairEdges M hno hda hdb hm
    exact .closed (tb1Realization M hab hnd hmem hda hdb data)
  · let data : MixedPairEdges M a b 3 0 1 := mixedPairEdges M hno hda hdb hm
    let c := data.right.neighbor 0
    have hc : c ∈ M.atoms := data.right.neighbor_mem 0
    have hca : c ≠ a := data.right.neighbor_ne_partner 0
    have hcb : c ≠ b := data.right.neighbor_ne_center 0
    have hnd : ([a,b,c] : List V).Nodup := by simp_all [ne_comm]
    have hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    exact .tail (tb2Realization M hab hnd hmem hda hdb data rfl)

/-- The source's exclusion of two degree-four triple endpoints forces one
of the two transcribed TB groups. -/
theorem exists_triple_selection (M : Molecule V D) (hM : M.IsMolecule) (hno : AppbNoLoops M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hm : M.bondsBetween a b = 3) (hnot : ¬(M.deg a = 4 ∧ M.deg b = 4)) : TripleSelection M := by
  have hcA := deg_le_four M hM ha
  have hcB := deg_le_four M hM hb
  have hloA := bondsBetween_le_degree M hab
  have hm' : M.bondsBetween b a = 3 := (bondsBetween_symm M b a).trans hm
  have hloB := bondsBetween_le_degree M hab.symm
  have hA : M.deg a = 3 ∨ M.deg a = 4 := by omega
  have hB : M.deg b = 3 ∨ M.deg b = 4 := by omega
  rcases hA with hA | hA
  · exact triple_selection_of_degree_three M hno ha hb hab hA hB hm
  · have hB' : M.deg b = 3 := by omega
    exact triple_selection_of_degree_three M hno hb ha hab.symm hB' (Or.inr hA) hm'

end WaveTurbulence.Mole.AppbAlgorithm

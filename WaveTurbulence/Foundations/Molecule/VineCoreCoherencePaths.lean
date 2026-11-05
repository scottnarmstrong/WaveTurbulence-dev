/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIntrinsicCoreGroups
import Mathlib.Tactic

/-! # Finite intrinsic paths connect every original coherence group -/

public section
namespace WaveTurbulence.Vine

/-- Literal counterpart of the graph-defined generating relation. -/
@[expose] def CoreCoherenceEdge (X : VineType) (i j : Fin X.template.n) : Prop :=
  2 ≤ i.1 ∧ 2 ≤ j.1 ∧
  ((i ≠ j ∧ 2 ≤ X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1)) ∨
    (CoreUndoubled X i ∧ CoreUndoubled X j) ∨
    (CoreUndoubled X i ∧ ∃ w : Fin X.template.n,2 ≤ w.1 ∧ j ≠ w ∧
      2 ≤ X.template.bonds.count (j.1,w.1)+X.template.bonds.count (w.1,j.1) ∧
      EdgeAdj X.template.bonds i.1 j.1 ∧ EdgeAdj X.template.bonds i.1 w.1))

instance (X : VineType) (i j : Fin X.template.n) : Decidable (CoreCoherenceEdge X i j) := by
  unfold CoreCoherenceEdge
  infer_instance

/-- Every original group is connected by at most two intrinsic generating
edges, allowing either orientation. -/
theorem template_group_intrinsic_paths (X : VineType) :
    ∀ g ∈ X.template.groups,∀ i j : Fin X.template.n,i.1 ∈ g → j.1 ∈ g →
    i=j ∨ (CoreCoherenceEdge X i j ∨ CoreCoherenceEdge X j i) ∨
      ∃ m : Fin X.template.n,(CoreCoherenceEdge X i m ∨ CoreCoherenceEdge X m i) ∧
        (CoreCoherenceEdge X m j ∨ CoreCoherenceEdge X j m) := by
  cases X <;> decide

/-- Any edge used by the undoubled triangle clause survives all insertions. -/
theorem template_triangle_attachment_unmarked (X : VineType) :
    ∀ i j w : Fin X.template.n,2 ≤ i.1 → 2 ≤ j.1 → 2 ≤ w.1 →
    CoreUndoubled X i → j ≠ w →
    2 ≤ X.template.bonds.count (j.1,w.1)+X.template.bonds.count (w.1,j.1) →
    EdgeAdj X.template.bonds i.1 j.1 → EdgeAdj X.template.bonds i.1 w.1 →
    ∀ s ∈ X.template.slots,
      ((i.1,j.1) ≠ s.1 ∧ (i.1,j.1) ≠ s.2) ∧
      ((j.1,i.1) ≠ s.1 ∧ (j.1,i.1) ≠ s.2) := by
  cases X <;> decide

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreDoubleGroups
public import WaveTurbulence.Foundations.Molecule.VinePaths
import Mathlib.Tactic

/-! # Literal joint-free triangles lie in the prescribed coherence group -/

public section
namespace WaveTurbulence.Vine

/-- TARGET cohmol: every triangle of three distinct nonjoint core atoms
belongs to one prescribed three-atom group. Type III is included even
though only one of its three sides is doubled. -/
theorem template_triangle_same_group (X : VineType) :
    ∀ i j k : Fin X.template.n,2 ≤ i.1 → 2 ≤ j.1 → 2 ≤ k.1 →
    i ≠ j → j ≠ k → i ≠ k →
    EdgeAdj X.template.bonds i.1 j.1 → EdgeAdj X.template.bonds j.1 k.1 →
    EdgeAdj X.template.bonds i.1 k.1 →
    ∃ q : Fin X.template.groups.length,X.template.groups[q.1].length=3 ∧
      i.1 ∈ X.template.groups[q.1] ∧ j.1 ∈ X.template.groups[q.1] ∧
      k.1 ∈ X.template.groups[q.1] := by
  cases X <;> decide

/-- The exceptional type-VII pair is a single bond, so it must be treated
separately from the doubled-pair rule in TARGET cohmol. -/
theorem typeVII_exceptional_pair_single :
    VineType.VII.template.bonds.count (7,8)=1 ∧
    VineType.VII.template.bonds.count (8,7)=0 ∧
    [7,8] ∈ VineType.VII.template.groups := by decide

end WaveTurbulence.Vine

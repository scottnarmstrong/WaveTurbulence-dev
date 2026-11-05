/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # Vine template checks (TARGET defvine and cohmol)

The pinned B2 bodies are imported unchanged. Edges retain multiplicity.
-/

public section
namespace WaveTurbulence.Vine

/-- The undirected incidence count, with loops counted twice. -/
@[expose] def templateDegree (T : VineTemplate) (v : ℕ) : ℕ :=
  ((T.bonds.map Prod.fst).count v) + ((T.bonds.map Prod.snd).count v)

/-- TARGET defvine: every template has two degree-two joints and
all other atoms have degree four. -/
theorem template_degrees (X : VineType) :
    ∀ v < X.template.n, templateDegree X.template v = if v < 2 then 2 else 4 := by
  cases X <;> intro v hv <;> norm_num [VineType.template] at hv
  all_goals interval_cases v <;> rfl

/-- Every template edge has endpoints in the actual atom range. -/
theorem template_endpoints (X : VineType) :
    ∀ e ∈ X.template.bonds, e.1 < X.template.n ∧ e.2 < X.template.n := by
  cases X <;> decide

/-- The number of template bonds is twice the atom count minus two. -/
theorem template_bond_count (X : VineType) :
    X.template.bonds.length + 2 = 2*X.template.n := by
  cases X <;> rfl

/-- TARGET defvine: precisely types I and II are bad. -/
theorem isBad_iff (X : VineType) : X.IsBad = true ↔ X = .I ∨ X = .II := by
  cases X <;> simp [VineType.IsBad]

/-- TARGET cohmol: groups partition the non-joint atoms without repetition. -/
theorem template_groups_partition (X : VineType) :
    X.template.groups.flatten.Perm ((List.range X.template.n).drop 2) := by
  cases X <;> decide

/-- Every group in a base template has two or three atoms. -/
theorem template_group_sizes (X : VineType) :
    ∀ g ∈ X.template.groups, g.length = 2 ∨ g.length = 3 := by
  cases X <;> decide

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineOldBondCounts
public import WaveTurbulence.Foundations.Molecule.VineIncidence
import Mathlib.Tactic

/-! # Pair-restricted degree detects old bond multiplicity -/

public section
namespace WaveTurbulence.Vine

/-- One encoded edge contributes its two endpoint indicators to degree. -/
theorem edgeDegree_cons (a b v : ℕ) (es : List (ℕ×ℕ)) :
    edgeDegree ((a,b)::es) v=edgeDegree es v+(if a=v then 1 else 0)+(if b=v then 1 else 0) := by
  simp only [edgeDegree,List.map_cons,List.count_cons,beq_iff_eq]
  omega

/-- The induced degree at u in a two-label set counts a loop twice and
all unordered u-v edges once, with encoded orientation retained in the counts. -/
theorem edgeDegree_restrict_pair (es : List (ℕ×ℕ)) (u v : ℕ) (huv : u ≠ v) :
    edgeDegree (restrictBonds {u,v} es) u=2*es.count (u,u)+es.count (u,v)+es.count (v,u) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    by_cases hau : a=u <;> by_cases hbu : b=u <;> by_cases hav : a=v <;> by_cases hbv : b=v
    all_goals simp_all [restrictBonds,edgeDegree_cons]
    all_goals omega

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
import Mathlib.Tactic

/-! # Distinct-endpoint reinsertion preserves the exclusion of self-loops -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_addBond_noLoops (M : Molecule V D) (a b : V)
    (h : AppbNoLoops M) (hab : a ≠ b) : AppbNoLoops (addBond M a b) := by
  rintro (x|t)
  · exact h x
  · cases t
    · exact hab.symm
    · exact hab

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem postWithBond_noLoops (a b : ℕ) (h : AppbNoLoops M)
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hab : a ≠ b) :
    AppbNoLoops (r.postWithBond a b) := by
  apply appb_addBond_noLoops
  · intro x
    exact h x.val
  · exact fun he => hab (r.vertex_injective ha hb he)

theorem directedPostWithBond_noLoops (a b : ℕ) (i : Fin P.edges.length)
    (h : AppbNoLoops M) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hab : a ≠ b) :
    AppbNoLoops (r.directedPostWithBond a b i) := by
  unfold directedPostWithBond
  split_ifs
  · exact r.postWithBond_noLoops a b h ha hb hab
  · exact r.postWithBond_noLoops b a h hb ha hab.symm

end AppbRealization
end WaveTurbulence.Mole

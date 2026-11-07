/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # The atom set of either directed reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem directedPostWithBond_atoms (a b : ℕ) (i : Fin P.edges.length)
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hka : a ∉ P.removed) (hkb : b ∉ P.removed) :
    (r.directedPostWithBond a b i).atoms = M.atoms \ r.removedAtoms := by
  unfold directedPostWithBond
  split_ifs
  · exact r.postWithBond_atoms a b ha hb hka hkb
  · exact r.postWithBond_atoms b a hb ha hkb hka

end AppbRealization
end WaveTurbulence.Mole

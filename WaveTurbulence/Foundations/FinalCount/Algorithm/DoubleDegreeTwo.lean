/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoStarPatterns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ExpandRemoval
import Mathlib.Tactic

/-! # The source 2R-4F group is constructed from both actual degree-two endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {v : V} (st : Star M v 2)

noncomputable def closedDoubleRealization (hv : v ∈ M.atoms)
    (heq : st.neighbor 0 = st.neighbor 1) (hd : M.deg (st.neighbor 0) = 2) :
    AppbRealization M AppbPatternKind.r24.pattern := by
  let r := st.doubleRealization hv heq
  apply expandRemoved r {1,2} (by decide) (by decide)
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact (r.deleted_degree 1 (by decide))
  · have ha' : a = 2 := mem_singleton.mp ha
    subst a
    change M.deg (st.neighbor 0) = 2
    exact hd

end Star
end WaveTurbulence.Mole.AppbAlgorithm

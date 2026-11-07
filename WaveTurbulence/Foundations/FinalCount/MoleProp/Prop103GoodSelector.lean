/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodTwo
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodThree
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodFour
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodBeta
import Mathlib.Tactic

/-! # The actual source good-configuration selector for Proposition10.3

The source graph and the genuinely inspected R step are the only inputs.
Every star ordering, bridge side, OLD cut, and circuit loss is produced
inside the branch proofs. No good-step schedule or counting estimate is
assumed by this endpoint.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A source search input and an actual good R inspection produce one of
the complete actual geometrical configurations consumed by the local
counting bounds. There are no chosen-star, chosen-cut, or rank-loss
premises. -/
theorem select_actual_good_configuration (M : Molecule V D) (hI : SearchInput M)
    {a : V} (ha : a ∈ M.atoms) (ha3 : M.deg a = 3)
    (hgood : GoodAfterRemoval M a) : ActualGoodConfiguration M a := by
  classical
  rcases hgood with hdegree | hbeta
  · obtain ⟨b,hb,hgoodB⟩ := hdegree
    rcases (ordinaryDegreeGood_iff (eraseAtoms M {a}) b).mp hgoodB with
      ⟨hb2,hcount⟩ | ⟨hb3,hcount⟩ | ⟨hb4,hcount⟩
    · exact select_good_post_degree_two M hI ha ha3 hb hb2 hcount
    · exact select_good_post_degree_three M hI ha ha3 hb hb3 hcount
    · exact select_good_post_degree_four M hI ha ha3 hb hb4 hcount
  · exact select_good_post_beta M hI ha ha3 hbeta

end WaveTurbulence.MoleProp

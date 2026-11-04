/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedPairRecovery

/-! # Recovering every child-couple carrier of a type-1 decomposition -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Each sign-oriented type-1 frame has incomparable roots. -/
theorem type1Frame_incomp (c : MiniCplCode) (j : Fin 3) :
    IncompAddr (type1Frame c j).1 (type1Frame c j).2 := by
  have hj := type1_frame_indices_ne c j
  exact ⟨fun h => hj h.1,fun h => hj h.1.symm⟩

/-- Once its mini-couple code is fixed, the carrier determines each of its three child carriers. -/
theorem type1_side_carrier_unique (c : MiniCplCode) (r g d r' g' d' : RegCpl)
    (he : decodedCouple (.type1 c r g d) = decodedCouple (.type1 c r' g' d')) (j : Fin 3) :
    decodedCouple (type1Side r g d j) = decodedCouple (type1Side r' g' d' j) := by
  let Q := RegCpl.type1 c r g d
  let R := RegCpl.type1 c r' g' d'
  have hf : coupleForest Q = coupleForest R := congrArg Garden.tree he
  have hC := type1_frame_extraction c r g d j
  have hD := type1_frame_extraction c r' g' d' j
  have ht : (type1Side r g d j).trees = (type1Side r' g' d' j).trees := by
    apply Prod.ext
    · have hx := hC.1
      change Comb.subtree (coupleForest Q (type1Frame c j).1.1) (type1Frame c j).1.2 = _ at hx
      rw [hf,hD.1] at hx
      exact (Option.some.inj hx).symm
    · have hx := hC.2
      change Comb.subtree (coupleForest Q (type1Frame c j).2.1) (type1Frame c j).2.2 = _ at hx
      rw [hf,hD.2] at hx
      exact (Option.some.inj hx).symm
  apply decodedCouple_eq_of_common_frame Q _ _ _ _ (type1Frame_incomp c j) ht
  · exact symmPairs_subset_of_pairs_subset (type1_frame_pair_inclusion c r g d j)
  · intro p hp
    have hr := symmPairs_subset_of_pairs_subset (type1_frame_pair_inclusion c r' g' d' j) p hp
    exact (symmPairs_eq_of_carrier_eq he p).mpr hr

/-- Equality of type-1 carriers recovers their mini-code and all three actual child carriers. -/
theorem type1_components_unique (c e : MiniCplCode) (r g d r' g' d' : RegCpl)
    (he : decodedCouple (.type1 c r g d) = decodedCouple (.type1 e r' g' d')) :
    c = e ∧ decodedCouple r = decodedCouple r' ∧
      decodedCouple g = decodedCouple g' ∧ decodedCouple d = decodedCouple d' := by
  have hc := type1_miniCode_unique c e r g d r' g' d' he
  subst e
  exact ⟨rfl,type1_side_carrier_unique c r g d r' g' d' he 0,
    type1_side_carrier_unique c r g d r' g' d' he 1,
    type1_side_carrier_unique c r g d r' g' d' he 2⟩

end WaveTurbulence.Reg

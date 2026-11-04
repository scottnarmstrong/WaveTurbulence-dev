/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedSubCouples

/-! # The actual three sub-couples of a type-1 decoding -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Select red, green or blue in source order. -/
def type1Side (r g d : RegCpl) (j : Fin 3) : RegCpl := ![r,g,d] j

/-- The actual sign-oriented child-root frame in source order. -/
def type1Frame (c : MiniCplCode) (j : Fin 3) : (Fin 2 × Path) × (Fin 2 × Path) :=
  ![((0,[0]),(1,[c.partner 0])),((1,[1]),(0,[1])),((0,[2]),(1,[c.partner 2]))] j

/-- Both selected roots extract exactly the selected code's two trees. -/
theorem type1_frame_extraction (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    Comb.subtree (coupleForest (.type1 c r g d) (type1Frame c j).1.1) (type1Frame c j).1.2 =
      some (type1Side r g d j).trees.1 ∧
    Comb.subtree (coupleForest (.type1 c r g d) (type1Frame c j).2.1) (type1Frame c j).2.2 =
      some (type1Side r g d j).trees.2 := by
  fin_cases j <;> fin_cases c <;>
    simp [type1Frame,type1Side,coupleForest,RegCpl.trees,Comb.subtree,MiniCplCode.partner]

/-- The selected pair block is literally included in the ambient source pair list. -/
theorem type1_frame_pair_inclusion (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    ∀ p ∈ (type1Side r g d j).pairsAt (type1Frame c j).1 (type1Frame c j).2,
      p ∈ (RegCpl.type1 c r g d).raw.2 := by
  fin_cases j <;> intro p hp
  all_goals
    dsimp only [type1Side,type1Frame] at hp ⊢
    simp only [RegCpl.raw,RegCpl.pairsAt,List.mem_append]
    tauto

/-- Turn the actual selected first root into a node of the decoded carrier. -/
noncomputable def type1FirstNode (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    GNode (decodedCouple (.type1 c r g d)).tree :=
  ⟨(type1Frame c j).1,(Comb.subtree_exists_iff _ _).mp
    ⟨_,(type1_frame_extraction c r g d j).1⟩⟩

/-- Turn the actual selected second root into a node of the decoded carrier. -/
noncomputable def type1SecondNode (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    GNode (decodedCouple (.type1 c r g d)).tree :=
  ⟨(type1Frame c j).2,(Comb.subtree_exists_iff _ _).mp
    ⟨_,(type1_frame_extraction c r g d j).2⟩⟩

/-- Each of the three child pairings is an actual completely paired sub-couple. -/
theorem type1_side_subCouple (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    Comb.IsSubCouple (decodedCouple (.type1 c r g d))
      (type1FirstNode c r g d j) (type1SecondNode c r g d j) :=
  subCouple_of_decoded_block (.type1 c r g d) (type1Side r g d j) _ (decodedCouple_decodes _)
    _ _ (type1_frame_extraction c r g d j).1 (type1_frame_extraction c r g d j).2
    (type1_frame_pair_inclusion c r g d j)

/-- Both roots of every inserted child couple lie in different original trees. -/
theorem type1_frame_indices_ne (c : MiniCplCode) (j : Fin 3) :
    (type1Frame c j).2.1 ≠ (type1Frame c j).1.1 := by
  fin_cases j <;> norm_num [type1Frame]

/-- Property L at each sign-oriented first child root is supplied by a genuine cross-root pair. -/
theorem type1_first_hasExternal (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    HasExternal (decodedCouple (.type1 c r g d)) (type1FirstNode c r g d j) :=
  hasExternal_of_subCouple (type1_side_subCouple c r g d j) (type1_frame_indices_ne c j)

/-- Property L also holds at the other root of every selected child couple. -/
theorem type1_second_hasExternal (c : MiniCplCode) (r g d : RegCpl) (j : Fin 3) :
    HasExternal (decodedCouple (.type1 c r g d)) (type1SecondNode c r g d j) := by
  have hs : Comb.IsSubCouple (decodedCouple (.type1 c r g d))
      (type1SecondNode c r g d j) (type1FirstNode c r g d j) := by
    simpa only [Comb.IsSubCouple,Finset.union_comm] using type1_side_subCouple c r g d j
  exact hasExternal_of_subCouple hs (type1_frame_indices_ne c j).symm

end WaveTurbulence.Reg

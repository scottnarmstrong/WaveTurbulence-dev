/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type2ExternalChildren

/-! # The carrier distinguishes type 1 from nontrivial type 2 -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Every one of the six root children has property L in a type-1 carrier. -/
theorem type1_all_children_external (c : MiniCplCode) (r g d : RegCpl) (t : Fin 2) (j : Fin 3) :
    ExternalAt (decodedCouple (.type1 c r g d)) (t,[j]) := by
  have h0 := (externalAt_iff_hasExternal _ _).mpr (type1_first_hasExternal c r g d 0)
  have h1 := (externalAt_iff_hasExternal _ _).mpr (type1_first_hasExternal c r g d 1)
  have h2 := (externalAt_iff_hasExternal _ _).mpr (type1_first_hasExternal c r g d 2)
  have h3 := (externalAt_iff_hasExternal _ _).mpr (type1_second_hasExternal c r g d 0)
  have h4 := (externalAt_iff_hasExternal _ _).mpr (type1_second_hasExternal c r g d 1)
  have h5 := (externalAt_iff_hasExternal _ _).mpr (type1_second_hasExternal c r g d 2)
  fin_cases t <;> fin_cases j <;> fin_cases c
  all_goals first
    | simpa [type1FirstNode,type1Frame,MiniCplCode.partner] using h0
    | simpa [type1FirstNode,type1Frame,MiniCplCode.partner] using h1
    | simpa [type1FirstNode,type1Frame,MiniCplCode.partner] using h2
    | simpa [type1SecondNode,type1Frame,MiniCplCode.partner] using h3
    | simpa [type1SecondNode,type1Frame,MiniCplCode.partner] using h4
    | simpa [type1SecondNode,type1Frame,MiniCplCode.partner] using h5

/-- A nonempty chain on either side prevents a type-2 carrier from having type 1. -/
theorem type1_ne_type2 (c : MiniCplCode) (r g d q : RegCpl) (p n : RegChain)
    (hne : ¬ (p.isNil = true ∧ n.isNil = true)) :
    decodedCouple (.type1 c r g d) ≠ decodedCouple (.type2 p n q) := by
  intro he
  cases p with
  | pair k r' g' i s =>
    have hL := type1_all_children_external c r g d 0 k.red.1
    rw [he] at hL
    have hc := (type2_positive_child_external_iff k r' g' q i s n k.red.1).mp hL
    exact (miniTree_slots_separate k).1 hc
  | nil =>
    cases n with
    | nil => exact hne ⟨rfl,rfl⟩
    | pair k r' g' i s =>
      have hL := type1_all_children_external c r g d 1 k.red.1
      rw [he] at hL
      have hc := (type2_negative_child_external_iff k r' g' q i s .nil k.red.1).mp hL
      exact (miniTree_slots_separate k).1 hc

/-- In particular, well-formed type-2 data never decode to a type-1 carrier. -/
theorem type1_ne_wf_type2 (c : MiniCplCode) (r g d q : RegCpl) (p n : RegChain)
    (hw : (RegCpl.type2 p n q).wf = true) :
    decodedCouple (.type1 c r g d) ≠ decodedCouple (.type2 p n q) := by
  apply type1_ne_type2 c r g d q p n
  simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hw
  intro he
  rw [he.1,he.2] at hw
  simp at hw

end WaveTurbulence.Reg

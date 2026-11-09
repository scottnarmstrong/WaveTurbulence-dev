/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Inst.Data
public import WaveTurbulence.Foundations.TVine.Checker.Inst.Part0
public import WaveTurbulence.Foundations.TVine.Checker.Inst.Part1
public import WaveTurbulence.Foundations.TVine.Checker.Inst.Part2
public import WaveTurbulence.Foundations.TVine.Checker.Inst.Part3
public import WaveTurbulence.Foundations.TVine.Checker.Inst.Part4

/-!
# All instance certificates

`checkInst_of_mem`: every instance of `instList` passes `checkInst`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open Inst in
theorem instLit_all : instLit.all checkInst = true := by
  simp only [instLit, List.all_cons, List.all_nil, Bool.and_true,
    ok_00, ok_01, ok_02, ok_03, ok_04, ok_05, ok_06, ok_07, ok_08, ok_09,
    ok_10, ok_11, ok_12, ok_13, ok_14, ok_15, ok_16, ok_17, ok_18, ok_19,
    ok_20, ok_21, ok_22, ok_23, ok_24, ok_25, ok_26, ok_27, ok_28, ok_29,
    ok_30, ok_31, ok_32, ok_33, ok_34, ok_35, ok_36, ok_37, ok_38, ok_39,
    ok_40, ok_41, ok_42, ok_43, ok_44, ok_45, ok_46, ok_47, ok_48, ok_49,
    ok_50, ok_51, ok_52, ok_53, ok_54, ok_55, ok_56, ok_57, ok_58, ok_59,
    ok_60, ok_61, ok_62, ok_63, ok_64, ok_65, ok_66, ok_67, ok_68, ok_69,
    ok_70, ok_71, ok_72, ok_73, ok_74, ok_75, ok_76, ok_77, ok_78, ok_79,
    ok_80, ok_81, ok_82, ok_83, ok_84, ok_85, ok_86, ok_87, ok_88, ok_89,
    ok_90, ok_91, ok_92, ok_93, ok_94, ok_95, ok_96, Bool.true_and]

theorem checkInst_of_mem {q : CParam × JParam} (hq : q ∈ instList) : checkInst q = true := by
  rw [instList_eq] at hq
  exact List.all_eq_true.mp instLit_all q hq

end WaveTurbulence.TVine.Checker

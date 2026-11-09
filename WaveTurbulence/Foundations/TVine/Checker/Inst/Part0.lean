/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# Instance certificates 0–19

`checkInst q = true` by kernel evaluation (`decide +kernel`) for the instances 0–19 of `instLit`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker.Inst

theorem ok_00 : checkInst (⟨0, none⟩, .two 0 1 0 1) = true := by decide +kernel
theorem ok_01 : checkInst (⟨0, none⟩, .two 0 1 0 2) = true := by decide +kernel
theorem ok_02 : checkInst (⟨0, none⟩, .two 0 1 1 2) = true := by decide +kernel
theorem ok_03 : checkInst (⟨0, none⟩, .two 0 2 0 2) = true := by decide +kernel
theorem ok_04 : checkInst (⟨0, none⟩, .two 0 2 1 2) = true := by decide +kernel
theorem ok_05 : checkInst (⟨0, none⟩, .two 1 2 1 2) = true := by decide +kernel
theorem ok_06 : checkInst (⟨0, none⟩, .one 0 1) = true := by decide +kernel
theorem ok_07 : checkInst (⟨0, none⟩, .one 0 2) = true := by decide +kernel
theorem ok_08 : checkInst (⟨0, none⟩, .one 1 2) = true := by decide +kernel
theorem ok_09 : checkInst (⟨1, none⟩, .two 0 1 3 4) = true := by decide +kernel
theorem ok_10 : checkInst (⟨1, none⟩, .two 0 2 3 4) = true := by decide +kernel
theorem ok_11 : checkInst (⟨1, none⟩, .two 0 3 3 4) = true := by decide +kernel
theorem ok_12 : checkInst (⟨1, none⟩, .two 1 2 3 4) = true := by decide +kernel
theorem ok_13 : checkInst (⟨1, none⟩, .two 1 4 3 4) = true := by decide +kernel
theorem ok_14 : checkInst (⟨1, none⟩, .two 3 4 3 4) = true := by decide +kernel
theorem ok_15 : checkInst (⟨1, none⟩, .one 3 4) = true := by decide +kernel
theorem ok_16 : checkInst (⟨2, none⟩, .two 0 1 7 8) = true := by decide +kernel
theorem ok_17 : checkInst (⟨2, none⟩, .two 0 2 7 8) = true := by decide +kernel
theorem ok_18 : checkInst (⟨2, none⟩, .two 0 3 7 8) = true := by decide +kernel
theorem ok_19 : checkInst (⟨2, none⟩, .two 1 2 7 8) = true := by decide +kernel

end WaveTurbulence.TVine.Checker.Inst

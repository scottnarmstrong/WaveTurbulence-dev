/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# Instance certificates 60–79

`checkInst q = true` by kernel evaluation (`decide +kernel`) for the instances 60–79 of `instLit`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker.Inst

theorem ok_60 : checkInst (⟨1, some (0, 1, 2)⟩, .two 3 4 9 10) = true := by decide +kernel
theorem ok_61 : checkInst (⟨1, some (0, 2, 2)⟩, .two 3 4 9 10) = true := by decide +kernel
theorem ok_62 : checkInst (⟨1, some (0, 3, 2)⟩, .two 3 4 9 10) = true := by decide +kernel
theorem ok_63 : checkInst (⟨1, some (1, 2, 2)⟩, .two 3 4 9 10) = true := by decide +kernel
theorem ok_64 : checkInst (⟨1, some (1, 4, 2)⟩, .two 3 4 9 10) = true := by decide +kernel
theorem ok_65 : checkInst (⟨1, some (0, 1, 3)⟩, .two 3 4 13 14) = true := by decide +kernel
theorem ok_66 : checkInst (⟨1, some (0, 2, 3)⟩, .two 3 4 13 14) = true := by decide +kernel
theorem ok_67 : checkInst (⟨1, some (0, 3, 3)⟩, .two 3 4 13 14) = true := by decide +kernel
theorem ok_68 : checkInst (⟨1, some (1, 2, 3)⟩, .two 3 4 13 14) = true := by decide +kernel
theorem ok_69 : checkInst (⟨1, some (1, 4, 3)⟩, .two 3 4 13 14) = true := by decide +kernel
theorem ok_70 : checkInst (⟨2, some (0, 1, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_71 : checkInst (⟨2, some (0, 2, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_72 : checkInst (⟨2, some (0, 3, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_73 : checkInst (⟨2, some (1, 2, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_74 : checkInst (⟨2, some (1, 4, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_75 : checkInst (⟨2, some (3, 4, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_76 : checkInst (⟨2, some (3, 7, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_77 : checkInst (⟨2, some (4, 8, 1)⟩, .two 5 6 7 8) = true := by decide +kernel
theorem ok_78 : checkInst (⟨2, some (0, 1, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_79 : checkInst (⟨2, some (0, 2, 2)⟩, .two 7 8 9 10) = true := by decide +kernel

end WaveTurbulence.TVine.Checker.Inst

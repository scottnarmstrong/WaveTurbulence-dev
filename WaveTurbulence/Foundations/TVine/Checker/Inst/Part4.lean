/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# Instance certificates 80–96

`checkInst q = true` by kernel evaluation (`decide +kernel`) for the instances 80–96 of `instLit`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker.Inst

theorem ok_80 : checkInst (⟨2, some (0, 3, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_81 : checkInst (⟨2, some (1, 2, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_82 : checkInst (⟨2, some (1, 4, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_83 : checkInst (⟨2, some (3, 4, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_84 : checkInst (⟨2, some (3, 7, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_85 : checkInst (⟨2, some (4, 8, 2)⟩, .two 7 8 9 10) = true := by decide +kernel
theorem ok_86 : checkInst (⟨3, some (0, 1, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_87 : checkInst (⟨3, some (0, 2, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_88 : checkInst (⟨3, some (0, 3, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_89 : checkInst (⟨3, some (1, 2, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_90 : checkInst (⟨3, some (1, 4, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_91 : checkInst (⟨3, some (3, 4, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_92 : checkInst (⟨3, some (3, 7, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_93 : checkInst (⟨3, some (4, 8, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_94 : checkInst (⟨3, some (7, 8, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_95 : checkInst (⟨3, some (7, 11, 1)⟩, .two 5 6 11 12) = true := by decide +kernel
theorem ok_96 : checkInst (⟨3, some (8, 12, 1)⟩, .two 5 6 11 12) = true := by decide +kernel

end WaveTurbulence.TVine.Checker.Inst

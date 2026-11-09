/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# Instance certificates 40–59

`checkInst q = true` by kernel evaluation (`decide +kernel`) for the instances 40–59 of `instLit`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker.Inst

theorem ok_40 : checkInst (⟨4, none⟩, .two 0 2 15 16) = true := by decide +kernel
theorem ok_41 : checkInst (⟨4, none⟩, .two 0 3 15 16) = true := by decide +kernel
theorem ok_42 : checkInst (⟨4, none⟩, .two 1 2 15 16) = true := by decide +kernel
theorem ok_43 : checkInst (⟨4, none⟩, .two 1 4 15 16) = true := by decide +kernel
theorem ok_44 : checkInst (⟨4, none⟩, .two 3 4 15 16) = true := by decide +kernel
theorem ok_45 : checkInst (⟨4, none⟩, .two 3 7 15 16) = true := by decide +kernel
theorem ok_46 : checkInst (⟨4, none⟩, .two 4 8 15 16) = true := by decide +kernel
theorem ok_47 : checkInst (⟨4, none⟩, .two 7 8 15 16) = true := by decide +kernel
theorem ok_48 : checkInst (⟨4, none⟩, .two 7 11 15 16) = true := by decide +kernel
theorem ok_49 : checkInst (⟨4, none⟩, .two 8 12 15 16) = true := by decide +kernel
theorem ok_50 : checkInst (⟨4, none⟩, .two 11 12 15 16) = true := by decide +kernel
theorem ok_51 : checkInst (⟨4, none⟩, .two 11 15 15 16) = true := by decide +kernel
theorem ok_52 : checkInst (⟨4, none⟩, .two 12 16 15 16) = true := by decide +kernel
theorem ok_53 : checkInst (⟨4, none⟩, .two 15 16 15 16) = true := by decide +kernel
theorem ok_54 : checkInst (⟨4, none⟩, .one 15 16) = true := by decide +kernel
theorem ok_55 : checkInst (⟨1, some (0, 1, 1)⟩, .two 3 4 5 6) = true := by decide +kernel
theorem ok_56 : checkInst (⟨1, some (0, 2, 1)⟩, .two 3 4 5 6) = true := by decide +kernel
theorem ok_57 : checkInst (⟨1, some (0, 3, 1)⟩, .two 3 4 5 6) = true := by decide +kernel
theorem ok_58 : checkInst (⟨1, some (1, 2, 1)⟩, .two 3 4 5 6) = true := by decide +kernel
theorem ok_59 : checkInst (⟨1, some (1, 4, 1)⟩, .two 3 4 5 6) = true := by decide +kernel

end WaveTurbulence.TVine.Checker.Inst

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# Instance certificates 20–39

`checkInst q = true` by kernel evaluation (`decide +kernel`) for the instances 20–39 of `instLit`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker.Inst

theorem ok_20 : checkInst (⟨2, none⟩, .two 1 4 7 8) = true := by decide +kernel
theorem ok_21 : checkInst (⟨2, none⟩, .two 3 4 7 8) = true := by decide +kernel
theorem ok_22 : checkInst (⟨2, none⟩, .two 3 7 7 8) = true := by decide +kernel
theorem ok_23 : checkInst (⟨2, none⟩, .two 4 8 7 8) = true := by decide +kernel
theorem ok_24 : checkInst (⟨2, none⟩, .two 7 8 7 8) = true := by decide +kernel
theorem ok_25 : checkInst (⟨2, none⟩, .one 7 8) = true := by decide +kernel
theorem ok_26 : checkInst (⟨3, none⟩, .two 0 1 11 12) = true := by decide +kernel
theorem ok_27 : checkInst (⟨3, none⟩, .two 0 2 11 12) = true := by decide +kernel
theorem ok_28 : checkInst (⟨3, none⟩, .two 0 3 11 12) = true := by decide +kernel
theorem ok_29 : checkInst (⟨3, none⟩, .two 1 2 11 12) = true := by decide +kernel
theorem ok_30 : checkInst (⟨3, none⟩, .two 1 4 11 12) = true := by decide +kernel
theorem ok_31 : checkInst (⟨3, none⟩, .two 3 4 11 12) = true := by decide +kernel
theorem ok_32 : checkInst (⟨3, none⟩, .two 3 7 11 12) = true := by decide +kernel
theorem ok_33 : checkInst (⟨3, none⟩, .two 4 8 11 12) = true := by decide +kernel
theorem ok_34 : checkInst (⟨3, none⟩, .two 7 8 11 12) = true := by decide +kernel
theorem ok_35 : checkInst (⟨3, none⟩, .two 7 11 11 12) = true := by decide +kernel
theorem ok_36 : checkInst (⟨3, none⟩, .two 8 12 11 12) = true := by decide +kernel
theorem ok_37 : checkInst (⟨3, none⟩, .two 11 12 11 12) = true := by decide +kernel
theorem ok_38 : checkInst (⟨3, none⟩, .one 11 12) = true := by decide +kernel
theorem ok_39 : checkInst (⟨4, none⟩, .two 0 1 15 16) = true := by decide +kernel

end WaveTurbulence.TVine.Checker.Inst

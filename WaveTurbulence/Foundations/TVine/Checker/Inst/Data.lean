/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Check

/-!
# The instance family as data

`instLit` is `instList` written out (97 instances: closure parameters and joint placements); `instList_eq`
checks the equality by kernel evaluation.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

/-- The 97 instances, as data. -/
def instLit : List (CParam × JParam) := [
  (⟨0, none⟩, .two 0 1 0 1),
  (⟨0, none⟩, .two 0 1 1 2),
  (⟨0, none⟩, .two 0 1 0 2),
  (⟨0, none⟩, .two 1 2 1 2),
  (⟨0, none⟩, .two 0 2 1 2),
  (⟨0, none⟩, .two 0 2 0 2),
  (⟨0, none⟩, .one 0 1),
  (⟨0, none⟩, .one 1 2),
  (⟨0, none⟩, .one 0 2),
  (⟨1, none⟩, .two 0 1 3 4),
  (⟨1, none⟩, .two 1 2 3 4),
  (⟨1, none⟩, .two 0 2 3 4),
  (⟨1, none⟩, .two 0 3 3 4),
  (⟨1, none⟩, .two 3 4 3 4),
  (⟨1, none⟩, .two 1 4 3 4),
  (⟨1, none⟩, .one 3 4),
  (⟨2, none⟩, .two 0 1 7 8),
  (⟨2, none⟩, .two 1 2 7 8),
  (⟨2, none⟩, .two 0 2 7 8),
  (⟨2, none⟩, .two 0 3 7 8),
  (⟨2, none⟩, .two 3 4 7 8),
  (⟨2, none⟩, .two 1 4 7 8),
  (⟨2, none⟩, .two 3 7 7 8),
  (⟨2, none⟩, .two 7 8 7 8),
  (⟨2, none⟩, .two 4 8 7 8),
  (⟨2, none⟩, .one 7 8),
  (⟨3, none⟩, .two 0 1 11 12),
  (⟨3, none⟩, .two 1 2 11 12),
  (⟨3, none⟩, .two 0 2 11 12),
  (⟨3, none⟩, .two 0 3 11 12),
  (⟨3, none⟩, .two 3 4 11 12),
  (⟨3, none⟩, .two 1 4 11 12),
  (⟨3, none⟩, .two 3 7 11 12),
  (⟨3, none⟩, .two 7 8 11 12),
  (⟨3, none⟩, .two 4 8 11 12),
  (⟨3, none⟩, .two 7 11 11 12),
  (⟨3, none⟩, .two 11 12 11 12),
  (⟨3, none⟩, .two 8 12 11 12),
  (⟨3, none⟩, .one 11 12),
  (⟨4, none⟩, .two 0 1 15 16),
  (⟨4, none⟩, .two 1 2 15 16),
  (⟨4, none⟩, .two 0 2 15 16),
  (⟨4, none⟩, .two 0 3 15 16),
  (⟨4, none⟩, .two 3 4 15 16),
  (⟨4, none⟩, .two 1 4 15 16),
  (⟨4, none⟩, .two 3 7 15 16),
  (⟨4, none⟩, .two 7 8 15 16),
  (⟨4, none⟩, .two 4 8 15 16),
  (⟨4, none⟩, .two 7 11 15 16),
  (⟨4, none⟩, .two 11 12 15 16),
  (⟨4, none⟩, .two 8 12 15 16),
  (⟨4, none⟩, .two 11 15 15 16),
  (⟨4, none⟩, .two 15 16 15 16),
  (⟨4, none⟩, .two 12 16 15 16),
  (⟨4, none⟩, .one 15 16),
  (⟨1, some (0, 1, 1)⟩, .two 3 4 5 6),
  (⟨1, some (1, 2, 1)⟩, .two 3 4 5 6),
  (⟨1, some (0, 2, 1)⟩, .two 3 4 5 6),
  (⟨1, some (0, 3, 1)⟩, .two 3 4 5 6),
  (⟨1, some (1, 4, 1)⟩, .two 3 4 5 6),
  (⟨1, some (0, 1, 2)⟩, .two 3 4 9 10),
  (⟨1, some (1, 2, 2)⟩, .two 3 4 9 10),
  (⟨1, some (0, 2, 2)⟩, .two 3 4 9 10),
  (⟨1, some (0, 3, 2)⟩, .two 3 4 9 10),
  (⟨1, some (1, 4, 2)⟩, .two 3 4 9 10),
  (⟨1, some (0, 1, 3)⟩, .two 3 4 13 14),
  (⟨1, some (1, 2, 3)⟩, .two 3 4 13 14),
  (⟨1, some (0, 2, 3)⟩, .two 3 4 13 14),
  (⟨1, some (0, 3, 3)⟩, .two 3 4 13 14),
  (⟨1, some (1, 4, 3)⟩, .two 3 4 13 14),
  (⟨2, some (0, 1, 1)⟩, .two 5 6 7 8),
  (⟨2, some (1, 2, 1)⟩, .two 5 6 7 8),
  (⟨2, some (0, 2, 1)⟩, .two 5 6 7 8),
  (⟨2, some (0, 3, 1)⟩, .two 5 6 7 8),
  (⟨2, some (3, 4, 1)⟩, .two 5 6 7 8),
  (⟨2, some (1, 4, 1)⟩, .two 5 6 7 8),
  (⟨2, some (3, 7, 1)⟩, .two 5 6 7 8),
  (⟨2, some (4, 8, 1)⟩, .two 5 6 7 8),
  (⟨2, some (0, 1, 2)⟩, .two 7 8 9 10),
  (⟨2, some (1, 2, 2)⟩, .two 7 8 9 10),
  (⟨2, some (0, 2, 2)⟩, .two 7 8 9 10),
  (⟨2, some (0, 3, 2)⟩, .two 7 8 9 10),
  (⟨2, some (3, 4, 2)⟩, .two 7 8 9 10),
  (⟨2, some (1, 4, 2)⟩, .two 7 8 9 10),
  (⟨2, some (3, 7, 2)⟩, .two 7 8 9 10),
  (⟨2, some (4, 8, 2)⟩, .two 7 8 9 10),
  (⟨3, some (0, 1, 1)⟩, .two 5 6 11 12),
  (⟨3, some (1, 2, 1)⟩, .two 5 6 11 12),
  (⟨3, some (0, 2, 1)⟩, .two 5 6 11 12),
  (⟨3, some (0, 3, 1)⟩, .two 5 6 11 12),
  (⟨3, some (3, 4, 1)⟩, .two 5 6 11 12),
  (⟨3, some (1, 4, 1)⟩, .two 5 6 11 12),
  (⟨3, some (3, 7, 1)⟩, .two 5 6 11 12),
  (⟨3, some (7, 8, 1)⟩, .two 5 6 11 12),
  (⟨3, some (4, 8, 1)⟩, .two 5 6 11 12),
  (⟨3, some (7, 11, 1)⟩, .two 5 6 11 12),
  (⟨3, some (8, 12, 1)⟩, .two 5 6 11 12)]

theorem instList_eq : instList = instLit := by decide +kernel

end WaveTurbulence.TVine.Checker

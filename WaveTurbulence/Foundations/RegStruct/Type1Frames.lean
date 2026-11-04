/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.FrameStability

/-! # The three disjoint source frames in a type-1 couple -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

abbrev redFrame {w : ℕ} (c : MiniCplCode) (a b : Fin w × Path) :=
  (addrExt a [0],addrExt b [c.partner 0])

abbrev greenFrame {w : ℕ} (a b : Fin w × Path) := (addrExt b [1],addrExt a [1])

abbrev blueFrame {w : ℕ} (c : MiniCplCode) (a b : Fin w × Path) :=
  (addrExt a [2],addrExt b [c.partner 2])

/-- Extending two incomparable root frames preserves their separation. -/
theorem IncompAddr.extend {w : ℕ} {a b : Fin w × Path} (h : IncompAddr a b) (p q : Path) :
    IncompAddr (addrExt a p) (addrExt b q) := h.descendants (below_extend a p) (below_extend b q)

/-- The two mini-couple tables separate all three child pairings. -/
theorem miniCouple_slots_separate (c : MiniCplCode) :
    c.partner 0 ≠ 1 ∧ c.partner 2 ≠ 1 ∧ c.partner 0 ≠ c.partner 2 := by
  fin_cases c <;> decide

/-- Each inserted red side couple has incomparable roots. -/
theorem redFrame_incomp {w : ℕ} (c : MiniCplCode) {a b : Fin w × Path} (h : IncompAddr a b) :
    IncompAddr (redFrame c a b).1 (redFrame c a b).2 := h.extend _ _

theorem greenFrame_incomp {w : ℕ} {a b : Fin w × Path} (h : IncompAddr a b) :
    IncompAddr (greenFrame a b).1 (greenFrame a b).2 := h.symm.extend _ _

theorem blueFrame_incomp {w : ℕ} (c : MiniCplCode) {a b : Fin w × Path} (h : IncompAddr a b) :
    IncompAddr (blueFrame c a b).1 (blueFrame c a b).2 := h.extend _ _

/-- Red and green insertions occupy disjoint pairs of child subtrees. -/
theorem red_green_apart {w : ℕ} (c : MiniCplCode) {a b : Fin w × Path} (h : IncompAddr a b) :
    FramesApart (redFrame c a b) (greenFrame a b) := by
  refine ⟨h.extend _ _,incomp_distinct_children a 0 1 [] [] (by decide),?_,h.symm.extend _ _⟩
  exact incomp_distinct_children b _ _ [] [] (miniCouple_slots_separate c).1

/-- Red and blue insertions occupy disjoint pairs of child subtrees. -/
theorem red_blue_apart {w : ℕ} (c : MiniCplCode) {a b : Fin w × Path} (h : IncompAddr a b) :
    FramesApart (redFrame c a b) (blueFrame c a b) := by
  refine ⟨incomp_distinct_children a 0 2 [] [] (by decide),h.extend _ _,h.symm.extend _ _,?_⟩
  exact incomp_distinct_children b _ _ [] [] (miniCouple_slots_separate c).2.2

/-- Green and blue insertions occupy disjoint pairs of child subtrees. -/
theorem green_blue_apart {w : ℕ} (c : MiniCplCode) {a b : Fin w × Path} (h : IncompAddr a b) :
    FramesApart (greenFrame a b) (blueFrame c a b) := by
  refine ⟨h.symm.extend _ _,?_,incomp_distinct_children a 1 2 [] [] (by decide),h.extend _ _⟩
  exact incomp_distinct_children b _ _ [] [] (miniCouple_slots_separate c).2.1.symm

end WaveTurbulence.Reg

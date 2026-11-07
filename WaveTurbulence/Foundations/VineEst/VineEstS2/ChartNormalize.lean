/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartReindex

/-! # The normalized chart (R20 (1)): rung `0` is put on a rung adjacent to the lower joint `b`

`normalizeChart C` re-indexes `C` (by `FullVineChart.reindex`) so that rung `0` is an adjacent rung (both rung
atoms bonded to `b`) whenever one exists; otherwise it is `C`.  For a type-II vine of a garden an adjacent rung
always exists (`VineEstS3.exists_adjacent_rung`).  `Contract.lean` is not amended; V4's `chosenVineChart` and
`chainPieceChart` apply this normalization to the contract's choice.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence VineParamContract Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V} {X : VineType}

/-- Both rung atoms of rung `j` are bonded to `b`. -/
def Adj (C : FullVineChart M X S a b) (j : Fin C.indexing.shape.m) : Prop :=
  M.bondsBetween b (C.indexing.atom (C.indexing.shape.xSlot j)).1 ≠ 0 ∧
    M.bondsBetween b (C.indexing.atom (C.indexing.shape.ySlot j)).1 ≠ 0

open Classical in
/-- The normalized chart: rung `0` is put on an adjacent rung when one exists. -/
noncomputable def normalizeChart (C : FullVineChart M X S a b) : FullVineChart M X S a b :=
  if h : ∃ j, Adj C j then FullVineChart.reindex C (Equiv.swap ⟨0, Fin.pos h.choose⟩ h.choose) else C

theorem normalizeChart_shape (C : FullVineChart M X S a b) :
    (normalizeChart C).indexing.shape = C.indexing.shape := by
  unfold normalizeChart
  split_ifs <;> rfl

theorem normalizeChart_adj (C : FullVineChart M X S a b) (h : ∃ j, Adj C j) :
    ∃ h0 : 0 < (normalizeChart C).indexing.shape.m, Adj (normalizeChart C) ⟨0, h0⟩ := by
  classical
  have hpos : 0 < C.indexing.shape.m := Fin.pos h.choose
  unfold normalizeChart
  rw [dif_pos h]
  refine ⟨hpos, ?_⟩
  have e1 : (slotPerm C.indexing.shape (Equiv.swap ⟨0, Fin.pos h.choose⟩ h.choose))
      (C.indexing.shape.xSlot ⟨0, hpos⟩) = C.indexing.shape.xSlot h.choose := by
    rw [slotPerm, Equiv.coe_fn_mk, slotMap_xSlot]; simp
  have e2 : (slotPerm C.indexing.shape (Equiv.swap ⟨0, Fin.pos h.choose⟩ h.choose))
      (C.indexing.shape.ySlot ⟨0, hpos⟩) = C.indexing.shape.ySlot h.choose := by
    rw [slotPerm, Equiv.coe_fn_mk, slotMap_ySlot]; simp
  show M.bondsBetween b (C.indexing.atom ((slotPerm C.indexing.shape (Equiv.swap ⟨0, Fin.pos h.choose⟩ h.choose))
      (C.indexing.shape.xSlot ⟨0, hpos⟩))).1 ≠ 0 ∧
    M.bondsBetween b (C.indexing.atom ((slotPerm C.indexing.shape (Equiv.swap ⟨0, Fin.pos h.choose⟩ h.choose))
      (C.indexing.shape.ySlot ⟨0, hpos⟩))).1 ≠ 0
  rw [e1, e2]
  exact h.choose_spec

end WaveTurbulence.VineEstS2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cong
public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue6
import Mathlib.Tactic

/-!
# Symmetry of congruence

Reversal of a once-per-member batch: each operation has a reverse operation at its output
(`exists_reverse_op_false`, `exists_reverse_op_true`), and the reversed list is again a permutation of
the members.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Every LF operation has a reverse operation at its output returning the original state. -/
theorem familyOperation_exists_reverse {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    ∃ op' : FamilyOperation (p := p) (kind := kind) op.output i, op'.output = A := by
  rcases op with ⟨c, el, tc, cc, ε, con⟩
  cases ε
  · exact exists_reverse_op_false A i c el tc cc con
  · exact exists_reverse_op_true A i c el tc cc con

theorem familyBatch_append_skip {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (i : ι) : FamilyBatch p kind (L ++ [i]) A B := by
  induction h with
  | nil A => exact .skip i (.nil A)
  | skip j h ih => exact .skip j ih
  | apply op h ih => exact .apply op ih

theorem familyBatch_append_apply {L : List ι} {A B X : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (i : ι) (op' : FamilyOperation (p := p) (kind := kind) B i)
    (hX : op'.output = X) : FamilyBatch p kind (L ++ [i]) A X := by
  induction h with
  | nil A =>
    subst hX
    exact .apply op' (.nil _)
  | skip j h ih => exact .skip j (ih op' hX)
  | apply op h ih => exact .apply op (ih op' hX)

/-- A batch can be undone by the reversed batch. -/
theorem familyBatch_reverse {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) : FamilyBatch p kind L.reverse B A := by
  induction h with
  | nil A => exact .nil A
  | skip i h ih =>
    rw [List.reverse_cons]
    exact familyBatch_append_skip ih i
  | apply op h ih =>
    rw [List.reverse_cons]
    obtain ⟨op', hop'⟩ := familyOperation_exists_reverse op
    exact familyBatch_append_apply ih _ op' hop'

/-- **Congruence is symmetric** (GAP.congEquiv, symmetry). -/
theorem Congruent.symm [Fintype ι] {A B : FamilyReconstruction w ι}
    (h : Congruent p kind A B) : Congruent p kind B A := by
  obtain ⟨M, hM, hB⟩ := h
  exact ⟨M.reverse, (List.reverse_perm M).trans hM, familyBatch_reverse hB⟩

end WaveTurbulence.Stage1

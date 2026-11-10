/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Final
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon

/-! # Class combinatorics, part 1: moving an operation to the front (V5 Step 4b, step 4, WP-A)

`familyBatch_moveLeft`: the converse of Stage 1's `familyBatch_moveRight`.  An operation at `i` performed LAST in a batch over a
list `K ++ [i]` with `i ∉ K` can be performed FIRST: `FamilyBatch (i :: K)` (uses `Stage1.opsCommute_all`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LFTwist

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

theorem familyBatch_moveLeft (hc : Stage1.OpsCommute p kind w ι) (i : ι) :
    ∀ (K : List ι), i ∉ K → ∀ {X Y : FamilyReconstruction w ι},
      FamilyBatch p kind (K ++ [i]) X Y → FamilyBatch p kind (i :: K) X Y := by
  intro K
  induction K with
  | nil =>
    intro _ X Y h
    exact h
  | cons k K ih =>
    intro hi X Y h
    have hik : k ≠ i := fun e => hi (by simp [e])
    have hiK : i ∉ K := fun e => hi (List.mem_cons_of_mem _ e)
    cases h with
    | skip _ h1 =>
      have h2 := ih hiK h1
      cases h2 with
      | skip _ h3 => exact .skip i (.skip k h3)
      | apply op h3 => exact .apply op (.skip k h3)
    | apply op1 h1 =>
      have h2 := ih hiK h1
      cases h2 with
      | skip _ h3 => exact .skip i (.apply op1 h3)
      | apply op2 h3 =>
        obtain ⟨op2', op1', hop⟩ := hc X k i hik op1 op2
        refine .apply op2' (.apply op1' ?_)
        rw [hop]
        exact h3

/-- Concatenation of two reached regions. -/
theorem Reach.append {L1 L2 : List ι} {A B C : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {c' : ChainAt B.skeleton B.family} {c'' : ChainAt C.skeleton C.family}
    (h1 : Reach p kind L1 A c B c') (h2 : Reach p kind L2 B c' C c'') : Reach p kind (L1 ++ L2) A c C c'' := by
  induction h1 with
  | nil A c => exact h2
  | skip i h ih => exact .skip i (ih h2)
  | apply op h ih => exact .apply op (ih h2)

section Decomp
variable [Fintype ι] [DecidableEq ι] {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}

end Decomp

end WaveTurbulence.VineEstS4

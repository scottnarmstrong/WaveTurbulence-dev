/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder

/-! # Base case: with no twist available, `VineEstFull` is `Step3Statement` (V5 Step 4a)

Under `CoreVinesNoTwist` (TARGET L1841) no core member admits an LF operation, so every batch only skips, the class is
the singleton `{G}`, its only section is the start (state, region), and the twisted kernel at the start is the
single-garden kernel (the CL region data and the layering are unique).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section NoOp
variable {ι : Type*} {p : ℕ} {kind : Bool}

theorem batch_eq_of_noOperation {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hno : ∀ i, IsEmpty (FamilyOperation (p := p) (kind := kind) A i)) : B = A := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih hno
  | apply op h ih => exact (hno _).elim op

theorem reach_skips {A : FamilyReconstruction w ι} (c : ChainAt A.skeleton A.family) (L : List ι) :
    Reach p kind L A c A c := by
  induction L with
  | nil => exact .nil A c
  | cons i L ih => exact .skip i ih

end NoOp

end WaveTurbulence.VineEstS4

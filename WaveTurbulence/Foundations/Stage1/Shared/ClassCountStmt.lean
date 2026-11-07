/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Spine.Stage1Gate
import Mathlib.Tactic

/-!
# CLASSCOUNT (R39): the exact statement of the Stage 1 class count (TARGET L2236-L2252)

`Stage1Counts` clause (iv) bounds the number of congruence classes containing a piece with data
`(g, r) = (ḡ, ρ̄)`.  S2's classes are sets of canonical layered gardens, and every piece `π` of a class `c` is
`stage1PieceOf` of a garden of `c` (R32 (1)); distinct classes have disjoint members.  So (iv) follows from
the garden-level bound `ClassCountStmt`: any finite set of canonical layered gardens (Stage 1 carriers) that all
carry a piece with data `(g, r)` has at most `C₀^N (C₀ r)! (C₀ R)! C₂^{g+r}` elements.
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton

/-- The layered garden `LG` carries a Stage 1 piece `stage1PieceOf` with data `(ḡ, ρ̄) = (g, r)`: for some
skeleton `S`, replacement data `D` decoding `LG`, and prescription `σ`. -/
def HasPieceData (d : ℕ) {R : ℕ} (LG : LayeredGarden (2 * R)) (g r : ℕ) : Prop :=
  ∃ (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (σ : Prescription S),
    (stage1PieceOf d hS LG hd σ).gbar = g ∧ (stage1PieceOf d hS LG hd σ).rbar = r

/-- **The class count (TARGET finalprooffin, L2236-L2252), garden form.** -/
def ClassCountStmt : Prop :=
  ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, Stage1Carries P p N LG ∧ HasPieceData P.d LG g r) →
      (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
        P.C₂ ^ (g + r)

end WaveTurbulence.ClassCount

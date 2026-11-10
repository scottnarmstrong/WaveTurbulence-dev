/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
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

/-- B1b-2: an admissibility predicate for marked vine sets (`Adm LG S Mk`: `Mk` may be used on the skeleton `S` of
the layered garden `LG`). `fun _ _ Mk => Mk = ∅` is main's Stage 1; the world chooses the markings of Stage 1′. -/
abbrev MarkAdm := ∀ {R : ℕ} (_LG : LayeredGarden (2 * R)) (S : Garden (2 * R)), Set (Stage1.CLVine S) → Prop

/-- B1b-2: `LG` carries a Stage 1′ piece (`stage1PieceOf … σ Mk`, runs spliced at the admissible marked set `Mk`) with
data `(ḡ, ρ̄) = (g, r)`. -/
def HasPieceDataMk (Adm : MarkAdm) (d : ℕ) {R : ℕ} (LG : LayeredGarden (2 * R)) (g r : ℕ) : Prop :=
  ∃ (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (σ : Prescription S) (Mk : Set (Stage1.CLVine S)), Adm LG S Mk ∧
    (stage1PieceOf d hS LG hd σ Mk).gbar = g ∧ (stage1PieceOf d hS LG hd σ Mk).rbar = r

/-- B1b-2: **the class count for Stage 1′ pieces** at admissible marked sets (truncation-free carrier). The B2c/B4
target behind `prod_stage1CountsMk`; at `Adm = (· = ∅)` it is `ClassCountStmtW` (`classCountStmtW_of_Mk`). -/
def ClassCountStmtMk (Adm : MarkAdm) : Prop :=
  ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG ∧ HasPieceDataMk Adm P.d LG g r) →
      (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
        P.C₂ ^ (g + r)

end WaveTurbulence.ClassCount

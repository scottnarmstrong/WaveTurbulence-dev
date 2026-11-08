/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Sum

/-! # D7 SEL-RES: exports and exact-type examples

R179: the selected filter is `chiDN` (`FinalMKDefs/PieceSel.lean`). D7-2 (finding F-C5b-1): the per-tree forms
`markedPieceBoundSelAtT_of_one_le_d`, `markedSumBoundSelAtT`, `markedSumBoundSelT_of_gates`, `selSumTargetT`; the
single-scale exports are kept (`markedPieceBoundSelAt_of_one_le_d` is the per-tree bound at `Ms ≡ M₂`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs

/-- **`MarkedPieceSelTarget`** (D7's deliverable, C0's restated form with R175: `L^{(400d)·a}`, `1 ≤ P.d`). -/
theorem markedPieceSelTarget : MarkedPieceSelTarget :=
  fun _ _ hcP hcθ _ hd hs hc hf _ => markedPieceBoundSelAt_of_one_le_d hd hs hcP hcθ hc hf

/-- The selected piece bound and class sum chained, for `1 ≤ d`: only the two gates are hypotheses. -/
theorem markedSumBoundSel_of_gates {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMK P) (X : ℝ) (a : ℕ) (M₂ : ℝ) :
    MarkedSumBoundSelAt cP cθ X a M₂ P :=
  markedSumBoundSelAt hs X a M₂ hcθ (markedPieceBoundSelAt_of_one_le_d hd hs hcP hcθ hc hf)

/-- The selected piece bound and class sum chained with per-tree scales (finding F-C5b-1), for `1 ≤ d`. -/
theorem markedSumBoundSelT_of_gates {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMK P) (X : ℝ) :
    MarkedSumBoundSelAtT cP cθ X P :=
  markedSumBoundSelAtT hs X hcθ (markedPieceBoundSelAtT_of_one_le_d hd hs hcP hcθ hc hf)

/-- **`SelSumTargetT`** (C5b's D7 input, finding F-C5b-1): the per-tree selected class sum under `1 ≤ d`,
`PieceSmall` and the gates. -/
theorem selSumTargetT : SelSumTargetT :=
  fun _ _ hcP hcθ _ hd hs hc hf _ X => markedSumBoundSelT_of_gates hd hs hcP hcθ hc hf X

example : MarkedPieceSelTarget := markedPieceSelTarget

example : SelSumTargetT := selSumTargetT

example {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ)
    (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMK P) : MarkedPieceBoundSelAtT cP cθ P :=
  markedPieceBoundSelAtT_of_one_le_d hd hs hcP hcθ hc hf

example {P : WTParams} (hs : PieceSmall P) {cP cθ : ℝ} (X : ℝ) (hcθ : 1 ≤ cθ)
    (h : MarkedPieceBoundSelAtT cP cθ P) : MarkedSumBoundSelAtT cP cθ X P := markedSumBoundSelAtT hs X hcθ h

example : ∃ ψ : SchwartzMap ℝ ℂ, (∀ u, ψ u = (MkDefs.chiDN u : ℂ)) ∧ (∀ u, ‖ψ u‖ ≤ 1) ∧ ∃ u, ψ u ≠ 0 :=
  exists_schwartz_chiDN

example {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ)
    (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMK P) : MarkedPieceBoundSelAt cP cθ P :=
  markedPieceBoundSelAt_of_one_le_d hd hs hcP hcθ hc hf

example {P : WTParams} (hs : PieceSmall P) {cP cθ : ℝ} (X : ℝ) (a : ℕ) (M₂ : ℝ) (hcθ : 1 ≤ cθ)
    (h : MarkedPieceBoundSelAt cP cθ P) : MarkedSumBoundSelAt cP cθ X a M₂ P := markedSumBoundSelAt hs X a M₂ hcθ h

example {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ)
    (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMK P) (X : ℝ) (a : ℕ) (M₂ : ℝ) :
    MarkedSumBoundSelAt cP cθ X a M₂ P := markedSumBoundSel_of_gates hd hs hcP hcθ hc hf X a M₂

#print axioms markedPieceSelTarget
#print axioms markedPieceBoundSelAt_of_one_le_d
#print axioms markedSumBoundSelAt
#print axioms markedSumBoundSel_of_gates
#print axioms face_expand
#print axioms expand_bound
#print axioms point_bound
#print axioms markedPieceBoundSelAtT_of_one_le_d
#print axioms markedSumBoundSelAtT
#print axioms markedSumBoundSelT_of_gates
#print axioms selSumTargetT
#print axioms point_bound_atom
#print axioms expand_bound_atom
#print axioms exists_schwartz_chiDN

end WaveTurbulence.Flower.SelRes

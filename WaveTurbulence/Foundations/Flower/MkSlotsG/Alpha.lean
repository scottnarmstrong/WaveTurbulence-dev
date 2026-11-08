/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsG.Bridge
public import WaveTurbulence.Foundations.Flower.MkSlots.AlphaTop
public import WaveTurbulence.Foundations.Flower.MkSlots.IntPlan

/-! # B3s-HELPER6: the α case of the general piece and of the bridge

* **`pieceGen_alpha`**: for `pat ≡ plain`, `σ ≡ none`, `kSel ≡ none` the general piece is α's `pieceα`
  (no filter: `filtGen_alpha`; indicator = dagger indicator: `indGen_alpha`; no lower bound: `lbGen_plain`;
  `flwGen` = α's `flwOf`);
* `classRepGen_concl_of_alphaJ`: the conclusion of α's `ClassRepAlphaJ` (IntPlan) gives that of `ClassRepGen` in
  the α case, so α's bridge `markedClassRepresentsMKαJ_of_rep` is the α instance of `markedClassRepresentsMK_of_repGen`
  (after R187 α's `MarkedClassRepresentsMKαJ` keeps `lb` at its default `none` instead of in the `∃`, so B4's statement
  no longer specializes to it verbatim; `lbGen_plain` gives `lb = none` for the general piece in the α case). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (pieceα)

namespace WaveTurbulence.Flower.MkSlotsG

/-- **`pieceGen` is α's piece** for plain patterns, no capped-stem filter and no selection. -/
theorem pieceGen_alpha (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ) (Rs : Fin (2 * R) → ℝ)
    (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    pieceGen P J (fun _ => FixPat.plain) t s (fun _ => none) (fun _ => none) Rs mkF a dag =
      pieceα P J t s (fun _ => none) mkF a dag := by
  unfold pieceGen pieceα
  rw [filtGen_alpha, indGen_alpha, lbGen_plain]
  rfl

/-- **α compatibility (conclusions)**: at `pat ≡ plain`, `kSel ≡ none`, `σ ≡ none`, the conclusion of
`ClassRepAlphaJ` (IntPlan: the α piece at the class marking represents the class value at mass `b ^ N`) gives the
conclusion of `ClassRepGen` (no residual selected atom, `selMassMK = b ^ N`, `pieceGen = pieceα`, monotonicity in
`cP` for `1 ≤ L`). -/
theorem classRepGen_concl_of_alphaJ (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ)
    (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {N : ℕ} {cP b : ℝ} (hL : 1 ≤ P.L)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ}
    (h : (MkSlots.pieceAt P J t s (fun _ => none) a (classMk mkF a) dag).RepresentsIntMK N cP (fun _ => t) 0 roots
      (b ^ N) val) :
    RepresentsIntMKSel (pieceGen P J (fun _ => FixPat.plain) t s (fun _ => none) (fun _ => none) Rs mkF a dag)
        (selRGen J (fun _ => none) mkF a) N cP (fun _ => t) 0 roots
        (selMassMK N b Rs (fun _ => none) ((selRGen J (fun _ => none) mkF a).image fun v => v.1.1)) val ∧
      (pieceGen P J (fun _ => FixPat.plain) t s (fun _ => none) (fun _ => none) Rs mkF a dag).RepresentsIntMK N
        (cP + 343) (fun _ => t) 0 roots (b ^ N) val := by
  have h' : (pieceGen P J (fun _ => FixPat.plain) t s (fun _ => none) (fun _ => none) Rs mkF a dag).RepresentsIntMK
      N cP (fun _ => t) 0 roots (b ^ N) val := by
    rw [pieceGen_alpha]
    exact h
  refine ⟨?_, MkSlots.representsIntMK_mono_cP _ (by linarith) hL h'⟩
  rw [selRGen_none, MkSlots.selMassMK_none]
  exact (representsIntMKSel_empty _ N cP (fun _ => t) 0 roots (b ^ N) val).2 h'

end WaveTurbulence.Flower.MkSlotsG

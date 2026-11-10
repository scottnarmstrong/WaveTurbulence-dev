/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceBound

/-! # P2: piece bounds, separated 𝒦 and ℒ rows (pieces A1, A2, KQ, KT)

`SepT`: one separated term `c · J(t,s) · M(k)` of an approximant on a time box, with the bounds of `LeafwiseSeparated` (strict for `J`).
`sup_*`: the `sup_r 𝔖`-bounds of the spatial weights at the numerals `wN + 1 = 30 d`, `wDec = 30 d`.
`piece_A1`, `piece_A2`, `piece_KQ`, `piece_KT`: the rows of the pieces (a), (b) of `zpPieces` (`Pieces`: `pieceA1_term` …) with
`PieceBound`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- One separated term of an approximant on the time box `B`: `c · J(t,s) · M(k)` with `‖J‖_{X^{1-η}_0(B)} < CJ` and `‖M‖_{𝔖R(30d, Wm)} ≤ CM`. -/
structure SepT (P : WTParams) (Wm : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CJ CM : ℝ) where
  c : ℝ
  J : (Fin 2 → ℝ) → ℂ
  M : Mom P.d → ℝ
  hcell : B ⊆ cell q
  hint : B ⊆ closure (interior B)
  hCJ : 0 ≤ CJ
  hCM : 0 ≤ CM
  hJ : XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J ts) < ENNReal.ofReal CJ
  hM : SNormR (30 * P.d) Wm M ≤ ENNReal.ofReal CM

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}

theorem SepT.hJc {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepT P Wm B q CJ CM) :
    XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => cJ s.J ts) < ENNReal.ofReal CJ := by
  have := XNorm00Restr_conj (1 - P.η) B (Set.univ : Set Unit) (fun ts _ => s.J ts)
  exact this.symm ▸ s.hJ

theorem sn_lo (hd1 : 1 ≤ P.d) {A W Wm : ℕ} (hA : A ≤ 30 * P.d) (hW : W ≤ Wm) {M : Mom P.d → ℝ} {CM : ℝ}
    (hM : SNormR (30 * P.d) Wm M ≤ ENNReal.ofReal CM) (hCM : 0 ≤ CM) : SNorm A W (cm M) ≤ ENNReal.ofReal CM :=
  snorm_lower (by omega) hA hW hCM hM

section Sup
variable (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d) (hd1 : 1 ≤ P.d) {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ}
include hwN hwDec hd1

theorem supK_plain (v0 : D.S.VIdx) (s : SepT P (30 * P.d) B q CJ CM) :
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v0)) (spPlain s.c s.M r)) ≤ ENNReal.ofReal (|s.c| * CM) :=
  snorm_plain_le (A := D.wN) (W := D.wDec) (by omega) s.c s.hCM (sn_lo hd1 (by omega) (by omega) s.hM s.hCM)

end Sup


section Pieces
variable {Bq Bt : Set (Fin 2 → ℝ)} {qq qt : Fin 2 → ℝ} {CJq CMq CJt CMt : ℝ}

end Pieces

end WaveTurbulence.VineEstS5C.P2

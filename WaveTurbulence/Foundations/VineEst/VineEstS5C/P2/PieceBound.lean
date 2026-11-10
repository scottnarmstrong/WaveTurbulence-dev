/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Merge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.TimeModes
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.FSAe
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Pieces
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Mono
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.ConjNorm
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space

/-! # P2: the piece bounds, uniform output form (V5 Step 4d part C, step 7)

`Amb A P D`: the ambient engine data of one level (the hypotheses common to `level_SS/JS/SR/RS/RR`).  `PieceBound Z Kw Ks Lw Ls bK bL`: there are
rows `K, L` of the vine `Z.v0` with weights `Kw`, `Lw` (functions of the three clocks `c`, of `r` and of `k`) at the slots `Ks`, `Ls` whose merged
clocked expression obeys the engine bound with the row sizes `bK`, `bL`.  The theorems `piece_*` deliver this for each type of piece of
`zpPieces` from the separated data `(c, J, M)` of the approximants and the gate remainders.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- The `D`-independent hypotheses of the engine data of a level (a `Prop`, so constants depending on it depend on `(A, P)` only). -/
structure AmbP (A : ℝ) (P : WTParams) : Prop where
  hdb : SumintMixParDoubledAt A P
  hL : 0 < P.L
  hη0 : 0 < P.η
  hη1 : P.η ≤ 1 / 2
  hη4 : P.η < 1 / 4
  hC1 : 0 ≤ P.C₁
  hδ : 0 < P.δ
  hd1 : 1 ≤ P.d
  hθ' : 6 * P.η ^ 6 ≤ 1 - P.η
  hθη : 6 * P.η ^ 6 ≤ P.η
  hη3 : 3 * P.η ≤ 1

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}

end WaveTurbulence.VineEstS5C.P2

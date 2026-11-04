/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec
public import WaveTurbulence.Frozen.Defs.SumintDatumKVec
public import WaveTurbulence.Frozen.Defs.SumintDatumPhase
public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

/-!
# SumintDatum.expr

Wave B tier B1 (WaveB1-Sumint.lean), source: T L1608–L1611. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- **The expression `ℐ(t, t', t'', e, f, g, h)`** of (sumintI1) (T L1608–L1611), with the extra
factor `|r|` for each bad block of case (b). -/
noncomputable def expr (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (efgh : Fin 4 → Mom d) :
    ℂ :=
  let r := efgh 0 - efgh 1
  ((‖r‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (∏ v, D.wK v (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x r (tt 0) τ

end SumintDatum
end WaveTurbulence

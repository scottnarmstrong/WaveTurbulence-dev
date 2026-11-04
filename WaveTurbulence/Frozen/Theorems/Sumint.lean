/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible
public import WaveTurbulence.Frozen.Defs.SumintDatumExpr
public import WaveTurbulence.Frozen.Defs.SumintDatumM0
public import WaveTurbulence.Frozen.Defs.SumintDatumM1
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixA
public import WaveTurbulence.Frozen.Defs.XNorm00Restr
public import WaveTurbulence.Provider.Sumint

/-!
# sumint

Wave B tier B1 (WaveB1-Sumint.lean), source: T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B1.6 `sumint`** (T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6). For every admissible datum
with `I ≥ 1` and `M ≤ N_1^4`: with `ℬ = {(t,t',t'') ∈ ∏ [q,q+1] : t > max(t',t'')}` and `K` the set of
`(e,f,g,h) ∈ (w̲ + ℤ_L^d)^4` in the unit balls with `e - f = h - g = r ≠ 0`, `|r| ≤ L^{-γ+η}`,
`‖ℐ‖_{𝔛^{2η^8,0,0}(ℬ)} ≤ C₁ [max ⟨λ,μ,σ⟩]^{η^6} (C₁δ^{-1/2})^M L^{M(d-γ) - η²(|Bad| + M₁) - η^8 M₀ + η^7}`.
Deviations (WAVE-B v2 §4.6): (D1) weights on `ℝ^d` with the `ℝ^d` 𝔖-norm; (D2) `A` explicit (T: `C₀^M`);
(D3) unit intervals inside `[0, 𝔇]`; (D4) typo fixes (L1615 `A` = Nor; L1687 `j`); (D5) F23 (proof
obligation, not in the statement); (D6, G-4) the size hypothesis `M ≤ N_1^4`; (D7) the shifts
`h₁, h₂` are integer combinations of `(e,f,g,h)` with coefficient sum `1` and no constant lattice
offset (T: "vectors depending only on `(e,f,g,h)`"; if a consumer needs an offset, the datum gets
`c₁ c₂ : S.VIdx → (Fin d → ℤ)`, stage-3 O3 and question 3); (D8, stage-3 R6) every `Λ_v ≥ 1`. -/
theorem sumint : WTPrefixA fun A P =>
    ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 →
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => D.expr hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.sumint
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END

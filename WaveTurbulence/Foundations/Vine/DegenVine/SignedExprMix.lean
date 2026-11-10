/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintSigned

/-! # Statements: `signedExpr` weighted by a character mixture, and the prefix statement (DEGEN-VINE)

Light module (no proofs of `sumint`): the engine modules import only this file for the statement
`SumintMixSigned`; its proof is `DegenVine.sumintMixSigned` (heavy closure on `SumintSigned.*`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence WaveTurbulence.VineEstS2 MeasureTheory Set
open scoped ENNReal

/-- `signedExpr` with the lattice sum weighted by the mixture `M`. -/
noncomputable def signedExprMix {d : ℕ} (D : WaveTurbulence.SumintDatum d)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (M : CharMix D.S d) (hI : 0 < D.S.I) (L γ δ η : ℝ)
    (tt : Fin 3 → ℝ) (efgh : Fin 4 → Mom d) : ℂ :=
  let r := efgh 0 - efgh 1
  ((‖r‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (M.val L efgh x * ∏ v, D.wK v (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), signedPhase D coreFirstSign coreSign L γ δ η x r (tt 0) τ

end WaveTurbulence.DegenVine

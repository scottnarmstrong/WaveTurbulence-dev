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

/-- **`sumint` with a character-mixture multiplier**, for the snapshot-9 datum with core signs. -/
def SumintMixSigned : Prop := WTPrefixA fun A P =>
    ∀ (D : WaveTurbulence.SumintDatum P.d) (hI : 0 < D.S.I) (coreFirstSign coreSign : Fin D.S.I → ℤˣ),
      D.Admissible A P.L P.γ P.η P.D → D.S.M ≤ P.N 1 ^ 4 → ∀ M : CharMix D.S P.d,
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K
          (fun tt v => signedExprMix D coreFirstSign coreSign M hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (M.mass * (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)))

end WaveTurbulence.DegenVine

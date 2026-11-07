/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Level

/-! # P4 (W2(a)): the engine bound with every row given (several operative vines at once)

P2's `vineLevel_bound` / `PieceBound` replace the two rows of ONE vine `v₀` in an ambient family `(cr₀, M₀)`.  A term of the unrolled class
sum has a piece at every operative vine, so we state the engine bound for a family of rows given row by row (`RowData` for every
`ρ : Row D`, each with its a.e. mode expansion): `allCR`, `allCM`, and **`allRows_bound`**: the restriction norm of the clocked expression
is at most `pre · ∏_ρ b_ρ` (`clockedBoundMix3`).  The pieces of P2 (`piece_*`) provide the `RowData` of the operative vines, the native rows
those of the others; no fold over the vines is needed.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d} {θ : ℝ}

/-- The clocked rows of a row-by-row family. -/
noncomputable def allCR (R : ∀ ρ : Row D, RowData D θ ρ) : ClockedRows3 D where
  W ρ := (R ρ).W
  slot ρ := (R ρ).slot
  W_indep v c r r' k := (R (Sum.inr v)).indepW v rfl c r r' k

/-- The mode families of a row-by-row family. -/
noncomputable def allCM (R : ∀ ρ : Row D, RowData D θ ρ) : ClockedModes3 D θ where
  c ρ := (R ρ).c
  c_indep v m r r' k := (R (Sum.inr v)).indepC v rfl m r r' k
  b ρ := (R ρ).b
  b_ne_top ρ := (R ρ).b_ne_top
  fs_bound ρ := (R ρ).fs

theorem allCR_clock (R : ∀ ρ : Row D, RowData D θ ρ) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row D) :
    (allCR R).clock τ tt ρ = (R ρ).clk τ tt := rfl

/-- The a.e. expansion of all rows. -/
theorem allRows_hser (R : ∀ ρ : Row D, RowData D θ ρ) (hI : 0 < D.S.I) (hAe : ∀ ρ, (R ρ).Ae hI) :
    ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ (ρ : Row D) (r k : Mom d),
      HasSum (fun m => (allCM R).c ρ m r k * fsPhase m ((allCR R).clock τ tt ρ)) ((allCR R).W ρ ((allCR R).clock τ tt ρ) r k) := by
  intro tt htt
  have h := ae_all_iff.2 fun ρ : Row D => hAe ρ tt htt
  filter_upwards [h] with τ hτ ρ r k
  exact hτ ρ r k

/-- **The engine bound with every row given.** -/
theorem allRows_bound {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (R : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (R ρ).Ae hI) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (allCR R) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, (R ρ).b :=
  clockedBoundMix3 hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM (allCR R) (allCM R)
    (allRows_hser R hI hAe)

end WaveTurbulence.VineEstS5C.P4

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Engine
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Rows

/-! # P2: the engine datum of one operative vine level (V5 Step 4d part C, packet P2)

`RowData D θ ρ`: everything the arity-3 engine `clockedBoundMix3` asks of ONE weight row `ρ` (weight, three clock
slots, Fourier modes, mode size, a.e. expansion).  `mergeRows`: replace the two rows `𝒦 = inl v₀`, `ℒ = inr v₀` of the vine
`v₀` in an ambient family `(cr₀, M₀)` by two `RowData`.  **`vineLevel_bound`**: the `XNorm00Restr` bound of the merged
clocked expression, with the product of the mode sizes split as `b_𝒦 b_ℒ ∏_{other rows} b`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- The engine data of one weight row `ρ`: weight, slots, mode coefficients, mode size.  `indep`: an `ℒ` row does not
depend on `r` (weight and coefficients). -/
structure RowData (D : SumintPar.SumintDatum d) (θ : ℝ) (ρ : Row D) where
  W : (Fin 3 → ℝ) → Mom d → Mom d → ℂ
  slot : Fin 3 → VineEstS3Par.Eng.Slot D
  c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ
  b : ℝ≥0∞
  b_ne_top : b ≠ ⊤
  fs : coefBound θ D.wN (rowOrder D ρ) c ≤ b
  indepW : ∀ v, ρ = Sum.inr v → ∀ (c : Fin 3 → ℝ) (r r' k : Mom d), W c r k = W c r' k
  indepC : ∀ v, ρ = Sum.inr v → ∀ (m : Fin 3 → ℤ) (r r' k : Mom d), c m r k = c m r' k

/-- The clock triple of a row datum at internal times `τ` and external times `tt`. -/
def RowData.clk {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => slotVal D τ tt (R.slot i)

/-- The a.e. mode expansion of a row datum on the time domain (the form of `hser` of the engine, for one row). -/
def RowData.Ae {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (hI : 0 < D.S.I) : Prop :=
  ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ r k : Mom d,
    HasSum (fun m => R.c m r k * fsPhase m (R.clk τ tt)) (R.W (R.clk τ tt) r k)

section Merge
open Classical

variable {θ : ℝ}

end Merge

end WaveTurbulence.VineEstS5C.P2

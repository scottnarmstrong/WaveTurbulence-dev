/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PiProd

/-! # Expansion of a clocked `sumint` expression into modes (engine step EXP, interchange)

Given Fourier-series expansions `W_ρ(s,k) = ∑_m c_ρ(m,k) e^{πi m·s}` of the clocked weights, the clocked
`sumint` expression is the sum over mode tuples of `e^{πi ν_m · tt} · signedExpr (modeDatum ..)`, with the
interchange of `∑_x`, `∫_τ`, `∑_m` justified by the summable majorant `S ρ m · Dec ρ k`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem continuous_slotVal (tt : Fin 3 → ℝ) (s : Slot D) : Continuous fun τ : D.S.TVar → ℝ => slotVal D τ tt s := by
  cases s with
  | inl v => exact continuous_apply v
  | inr c => exact continuous_const


end WaveTurbulence.VineEstS3Par.Eng

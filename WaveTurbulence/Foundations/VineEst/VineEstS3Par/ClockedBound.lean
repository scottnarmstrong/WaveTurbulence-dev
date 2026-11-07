/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ModeBounds2
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedModes
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.OutMod

/-! # The engine constant (parametric-weights engine, V5 Step 4d)

Only `engineConst` of `VineEstS3.ClockedBound` is needed by the character-mixture engine
(`DegenVinePar.ClockedBoundMix`); the non-mixture `mode_bound` / `clockedBound` are superseded by it.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

/-- The `η`- and `|Row|`-dependent constant of the per-mode weight. -/
noncomputable def engineConst (η : ℝ) (K : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) * ((2 : ℝ) ^ (2 * η ^ 8 + η ^ 6) * 4 ^ (η ^ 6)) ^ K

theorem engineConst_nonneg (η : ℝ) (K : ℕ) : 0 ≤ engineConst η K := by
  unfold engineConst; positivity



end WaveTurbulence.VineEstS3Par.Eng

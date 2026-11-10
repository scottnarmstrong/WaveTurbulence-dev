/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedModes
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ModeBounds2
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.OutMod

/-! # The engine: `sumint` for clock-dependent weights

The clocked `sumint` expression (weights depending on clocks through Fourier series on unit cells) obeys the
`sumint` bound with the weights' restriction norms `b ρ` in place of the normalised weight sizes.  It is
assembled from the mode expansion (`clockedExpr_hasSum`), the countable Minkowski inequality
(`XNorm00Restr_tsum_le`), the output modulation cost, the scaled `sumint` (`scaledSumintAt_of`) and the
per-mode weight (`mode_real_bound`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS2 Finset
  MeasureTheory
open scoped ENNReal

/-- The `η`- and `|Row|`-dependent constant of the per-mode weight. -/
noncomputable def engineConst (η : ℝ) (K : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) * ((2 : ℝ) ^ (2 * η ^ 8 + η ^ 6) * 4 ^ (η ^ 6)) ^ K

theorem engineConst_nonneg (η : ℝ) (K : ℕ) : 0 ≤ engineConst η K := by
  unfold engineConst; positivity



end WaveTurbulence.VineEstS3.Eng

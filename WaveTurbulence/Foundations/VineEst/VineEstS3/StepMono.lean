/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
public import WaveTurbulence.Foundations.Vine.DegenVine.ScaledSumintMix
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint

/-! # Large-constant monotonicity of the three prefix statements used by Step 3

`LargeConstantMonotone A` (lg-spine `PrefixConjunction`) says that `A P` implies `A P'` for
`P' = {P with C₁ := c₁, C₂ := c₂}` with `c₁ ≥ C₁`, `c₂ ≥ C₂`.  It is what lets independently quantified
prefixes (the `sumint` statement with `ε`-mixtures, B2.2 and the 30d Prop 6.1 gate) be combined (`prefix_and`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine MeasureTheory Set
open scoped ENNReal

@[simp] theorem Rdown_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (k : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).Rdown k = P.Rdown k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [WTParams.Rdown, ih]

@[simp] theorem N_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).N p = P.N p := by
  simp only [WTParams.N, WTParams.R, Rdown_largeConstants]

end WaveTurbulence.VineEstS3

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.EpsCoef
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.ResFactor

/-!
# aNonlin

Wave B tier B1 (WaveB1-System.lean), source: T L553–L564. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **The nonlinearity `𝒞_ζ(f,g,h)_k(t)`** of (akeqn2) (T L553–L564), `ζ = ±1`:
`δ/(2L^{d-γ}) · (iζ) ∑_{k₁-k₂+k₃=k} ε_{k₁k₂k₃} e^{ζπiδL^{2γ}Ω t} f_{k₁} g_{k₂} h_{k₃}` (`tsum` over the
resonant set; absolutely convergent in the solution class). Same body as the landed `NLS.aNonlin`
(bridge `aNonlin_eq_nls`). -/
noncomputable def aNonlin {d : ℕ} (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ) *
    ∑' p : {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n},
      (epsCoef p.1.1 p.1.2.1 p.1.2.2 : ℂ) *
        Complex.exp (((ζ * Real.pi * δ * L ^ (2 * γ) *
          resFactor (latticePoint L p.1.1) (latticePoint L p.1.2.1) (latticePoint L p.1.2.2)
            (latticePoint L n) * t : ℝ) : ℂ) * Complex.I) * f p.1.1 * g p.1.2.1 * h p.1.2.2

end WaveTurbulence

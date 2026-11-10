/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.DuhamelKernelBound
public import WaveTurbulence.Frozen.Defs.PartialDeriv
import Mathlib.Tactic

/-!
# The time-integral operators in TARGET A.2–A.3

Literal oriented interval integrals are used, so the formulas apply for
all real times, including `t < s`. The oscillatory factors in A.3 are
`exp(i Γ Δt)` as printed, whereas Fourier modes use `exp(2π i ξt)`.
The momentum functions `Γ_j` need no continuity assumption (owner's
zero-order norm ruling, 2026-11-03).
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Fourier

/-- TARGET A.2, L2355: the rectangular cutoff Duhamel operator `ℐχ`. -/
@[expose] noncomputable def cutoffDoubleIntegral (χ : ℝ → ℝ)
    (F : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    ∫ u in (0 : ℝ)..t 0, ∫ v in (0 : ℝ)..t 1,
      (χ u : ℂ) * (χ v : ℂ) * F ![u, v]

/-- TARGET A.2, L2356: the triangular cutoff Duhamel operator `𝒥χ`, on one time slice. -/
@[expose] noncomputable def cutoffTriangleIntegral (χ : ℝ → ℝ)
    (F : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    ∫ u in t 1..t 0, ∫ v in t 1..u, (χ u : ℂ) * (χ v : ℂ) * F ![u, v]

/-- TARGET A.2's momentum-dependent `𝒥χ`. -/
@[expose] noncomputable def cutoffJ {d : ℕ} (χ : ℝ → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  cutoffTriangleIntegral χ (fun u => F u k) t

/-- TARGET A.3, L2385–L2387: the fourfold ordered operator `𝒱χ`. -/
@[expose] noncomputable def cutoffV {d : ℕ} (χ : ℝ → ℝ) (Γ₁ Γ₂ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    ∫ u in t 1..t 0, ∫ a in t 1..u, ∫ b in t 1..a, ∫ v in t 1..b,
      (χ u : ℂ) * (χ a : ℂ) * (χ b : ℂ) * (χ v : ℂ) *
        Complex.exp ((Γ₁ k * (u - a) : ℝ) * Complex.I) *
        Complex.exp ((Γ₂ k * (b - v) : ℝ) * Complex.I) * F ![a, b] k

/-- The pointwise momentum supremum of time `L¹` norms, as used in TARGET A.2–A.3. -/
@[expose] noncomputable def uniformTimeL1 {d : ℕ}
    (F : (Fin 2 → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  ⨆ k, eLpNorm (fun t => F t k) 1

end WaveTurbulence.Fourier

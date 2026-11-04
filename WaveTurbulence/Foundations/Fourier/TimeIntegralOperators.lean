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

/-- TARGET A.3, L2384: the phase-modulated triangular operator `𝒰χ`. -/
@[expose] noncomputable def cutoffU {d : ℕ} (χ : ℝ → ℝ) (Γ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  cutoffTriangleIntegral χ
    (fun u => Complex.exp ((Γ k * (u 0 - u 1) : ℝ) * Complex.I) * F u k) t

/-- TARGET A.3, L2385–L2387: the fourfold ordered operator `𝒱χ`. -/
@[expose] noncomputable def cutoffV {d : ℕ} (χ : ℝ → ℝ) (Γ₁ Γ₂ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    ∫ u in t 1..t 0, ∫ a in t 1..u, ∫ b in t 1..a, ∫ v in t 1..b,
      (χ u : ℂ) * (χ a : ℂ) * (χ b : ℂ) * (χ v : ℂ) *
        Complex.exp ((Γ₁ k * (u - a) : ℝ) * Complex.I) *
        Complex.exp ((Γ₂ k * (b - v) : ℝ) * Complex.I) * F ![a, b] k

/-- The mixed time derivative in the RHS of TARGET A.3, using the frozen partial derivative. -/
@[expose] noncomputable def mixedTimePartial (F : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ :=
  WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 F)

/-- The pointwise momentum supremum of time `L¹` norms, as used in TARGET A.2–A.3. -/
@[expose] noncomputable def uniformTimeL1 {d : ℕ}
    (F : (Fin 2 → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  ⨆ k, eLpNorm (fun t => F t k) 1

/-- The tensor product DNY21 kernel in TARGET L2365–L2368. -/
@[expose] noncomputable def doubleDuhamelKernel (χ : ℝ → ℝ)
    (ξ ξ' : Fin 2 → ℝ) : ℂ :=
  duhamelKernel χ (ξ 0) (ξ' 0) * duhamelKernel χ (ξ 1) (ξ' 1)

/-- TARGET L2368 / DNY21 Lemma 3.1: the tensor kernel has four-bracket decay. -/
theorem norm_doubleDuhamelKernel_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (ξ ξ' : Fin 2 → ℝ) :
    ‖doubleDuhamelKernel χ ξ ξ'‖ ≤ duhamelDecayConstant χ ^ 2 /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 0 - ξ' 0) ^ 2) *
       Real.sqrt (1 + (ξ 1) ^ 2) * Real.sqrt (1 + (ξ 1 - ξ' 1) ^ 2)) := by
  have h0 := norm_duhamelKernel_le_brackets hχ hc (ξ 0) (ξ' 0)
  have h1 := norm_duhamelKernel_le_brackets hχ hc (ξ 1) (ξ' 1)
  have h := mul_le_mul h0 h1 (norm_nonneg _) ((norm_nonneg _).trans h0)
  rw [doubleDuhamelKernel, norm_mul]
  convert h using 1
  ring

end WaveTurbulence.Fourier

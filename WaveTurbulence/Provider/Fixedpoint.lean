/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ATr
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.IsSymmetricEvent
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Lop
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.ZNorm
public import WaveTurbulence.Frozen.Defs.ZSpace
import WaveTurbulence.Foundations.GammaLow.Glue.Fixedpoint
import WaveTurbulence.Foundations.GammaLow.Close.Final
import WaveTurbulence.Foundations.GammaLow.Close.Halves

/-!
# Provider for `WaveTurbulence.fixedpoint`

The proof of the frozen anchor `WaveTurbulence.fixedpoint` (T Prop `fixedpoint`, L780–L794; WAVE-B v2 §4.3) is assembled here under the export
`WaveTurbulence.Provider.fixedpoint`.
The proof is the L07 glue `GammaLow.Glue.fixedpoint_of_low` (`Foundations/GammaLow/Glue/Fixedpoint`:
`V2Chain.fixedpointS_of_parts` at `S = univ` from the full-range flower and layergarden estimates and
the sealed `wkeTaylor`) applied to the closed theorems `WaveTurbulence.GammaLow.Close.flower_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Final`) and `WaveTurbulence.GammaLow.Close.layergarden_low_closed`
(`WaveTurbulence.Foundations.GammaLow.Close.Halves`).
The proof modules are imported privately (`import`), so that the frozen anchor
elaborates its statement in its freeze environment. This module must not import its own frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- The frozen statement of `WaveTurbulence.fixedpoint`, verbatim,
proved by the assembly in the module docstring. -/
theorem fixedpoint : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∀ p : ℕ, p < P.D →
    ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F',
        let Ntr := P.N (p + 1)
        let Λ : ℝ := 5 / 4 * P.Lambda (p + 1)
        let ℒ : ℕ → (Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) →
            Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ :=
          fun j b t n => Lop P.L P.γ P.δ p Ntr (a ω p) j b t n
        let Zs := ZSpace (d := P.d) P.L Λ p
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p Ntr (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * Ntr)) ∧
        (∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : Icc (p : ℝ) (p + 1)) (n),
          ‖ℒ 0 b t n‖ ≤ jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(20 * Ntr : ℝ))) ∧
        (∀ b ∈ Zs, b - ℒ 1 b ∈ Zs) ∧
        (∀ c ∈ Zs, ∃! b, b ∈ Zs ∧ b - ℒ 1 b = c) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (3 * Ntr)) * ZNorm P.L Λ (b - ℒ 1 b)) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ∃ c ∈ Zs, c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b ∧
            ZNorm P.L Λ c ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ)))) ∧
        (∀ b ∈ Zs, ∀ b' ∈ Zs, ∀ c ∈ Zs, ∀ c' ∈ Zs,
          ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ZNorm P.L Λ b' ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b → c' - ℒ 1 c' = ℒ 0 b' + ℒ 2 b' + ℒ 3 b' →
          ZNorm P.L Λ (c - c') ≤ 2⁻¹ * ZNorm P.L Λ (b - b')) :=
  WaveTurbulence.GammaLow.Glue.fixedpoint_of_low WaveTurbulence.GammaLow.Close.flower_low_closed WaveTurbulence.GammaLow.Close.layergarden_low_closed

end WaveTurbulence.Provider

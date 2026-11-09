/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Frozen.Defs.NormLaplacian
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Frozen.Defs.SolvableEvent
public import WaveTurbulence.Frozen.Defs.KineticTime
import WaveTurbulence.Foundations.GammaLow.Glue.Main
import WaveTurbulence.Foundations.GammaLow.Close.Final
import WaveTurbulence.Foundations.GammaLow.Close.Halves

/-!
# Provider for `WaveTurbulence.main`

The proof of the frozen anchor `WaveTurbulence.main` (L314-L320 (Theorem 1.1, label main)) is assembled here under the export
`WaveTurbulence.Provider.main`.
The proof is the L07 glue `GammaLow.Glue.main_of_low` (`Foundations/GammaLow/Glue/Main`: main's
γ-generic `MainGlue.main_of_propansatz_nlsAkBridge` applied to the full-range propansatz and the sealed
`nlsAkBridge`) applied to the closed theorems `WaveTurbulence.GammaLow.Close.flower_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Final`) and `WaveTurbulence.GammaLow.Close.layergarden_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Halves`).
As in the sealed `wkelwp` and `main_v2` providers, `d` and `γ` are implicit and `hd`, `hγ` are
auto-params (`by assumption`), so that the anchor's body is `by exact WaveTurbulence.Provider.main`;
the conclusion is the anchor's, verbatim.
The proof modules are imported privately (`import`), so that the frozen anchor
elaborates its statement in its freeze environment. This module must not import its own frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence.Provider

universe u

/-- The frozen statement of `WaveTurbulence.main`, verbatim (binders `d`, `γ` implicit,
`hd`, `hγ` auto-params), proved by the assembly in the module docstring. -/
theorem main {d : ℕ} (hd : 3 ≤ d := by assumption) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1 := by assumption) :
    ∃ θ > (0 : ℝ), ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) →
      ∀ τstar > (0 : ℝ), ∀ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ →
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
        MeasurableSet (solvableEvent L α T φin g) ∧
        1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ P.real (solvableEvent L α T φin g) ∧
        ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
          (∀ ω ∈ solvableEvent L α T φin g,
            IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)) →
          ∀ t ∈ Icc 0 T, ∀ n : Fin d → ℤ,
            |(∫ ω, (solvableEvent L α T φin g).indicator
                  (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω ∂P)
              - φ (t / kineticTime α) (latticePoint L n)| ≤ L ^ (-θ) :=
  WaveTurbulence.GammaLow.Glue.main_of_low WaveTurbulence.GammaLow.Close.flower_low_closed WaveTurbulence.GammaLow.Close.layergarden_low_closed
    d hd γ hγ

end WaveTurbulence.Provider

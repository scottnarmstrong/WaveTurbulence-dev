/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Glue.Propansatz
public import WaveTurbulence.Foundations.XChain.MainAssembly
public import WaveTurbulence.Frozen.Theorems.NlsAkBridge
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

/-! # L0 GLUE: `main` (v1, Theorem 1.1 for `0 < γ < 1`) from FL-low and LG-low

Provider skeleton (conditional helper, distinct name). Main's γ-generic `MainGlue.main_of_propansatz_nlsAkBridge`
(`XChain/MainAssembly`, kept by the trimming guard) applied to `propansatz` (`propansatz_of_low`) and the sealed
`nlsAkBridge`. Its type is the type of the frozen DRAFT_SORRY anchor `WaveTurbulence.main`
(`Frozen/Theorems/Main.lean`), pasted verbatim, after the two hypotheses `hFL`, `hLG`. -/

public section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence.GammaLow.Glue

universe u

/-- **Deng–Hani Theorem 1.1 (`main`, v1, `0 < γ < 1`) from FL-low and LG-low.** -/
theorem main_of_low (hFL : WaveTurbulence.GammaLow.Flower.LayergardenFlowerLowGate) (hLG : WaveTurbulence.GammaLow.LGLow.LayergardenLowGate) (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
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
  MainGlue.main_of_propansatz_nlsAkBridge (propansatz_of_low hFL hLG) WaveTurbulence.nlsAkBridge d hd γ hγ

end WaveTurbulence.GammaLow.Glue

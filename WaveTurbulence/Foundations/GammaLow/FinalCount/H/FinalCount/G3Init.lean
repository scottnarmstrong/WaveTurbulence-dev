/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Init`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: the standing hypotheses on `M_sub` and the invariants along a whole run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem Run.good {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{_} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : Good R sf := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : Good R (St.init M₀) := ⟨hS.inv, St.init_clean M₀⟩
  have g1 := good_rtg (fun _ _ h g => Step1.good h g) h1 g0
  have g2 := good_rtg (fun _ _ h g => Step2.good h g) h2 g1
  have g3 := good_rtg (fun _ _ h g => Step3.good h g) h3 g2
  exact good_rtg (fun _ _ h g => Step4.good h g) h4 g3

end WaveTurbulence.GammaLow.FinalCount.H

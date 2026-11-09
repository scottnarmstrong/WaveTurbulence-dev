/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Final2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Final2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: the degree / classification / component part of DH23 Prop 9.5 (L1806--L1817) and TARGET
Prop `finalmol` (L2182--L2190), for the final molecule of a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Along a run, the state is flat. -/
theorem Run.flat {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : Flat sf := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : Good R (St.init M₀) := ⟨hS.inv, St.init_clean M₀⟩
  have r1 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h1 g0 (Flat.init hS)
  have r2 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f g.2⟩) h2 r1.1 r1.2
  have r3 := good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h3 r2.1 r2.2
  exact (good_flat_rtg (fun _ _ h g f => ⟨h.good g, h.flat f⟩) h4 r3.1 r3.2).2

/-- The structural part of Prop 9.5 for the final molecule of a run of the stage-2 algorithm. -/
theorem Run.finalStruct {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : FinalStruct R sf := by
  obtain ⟨hg, hC⟩ := hr.goodComp hS
  exact FinalStruct.of_good hg hC (hr.flat hS)

end WaveTurbulence.GammaLow.FinalCount.H

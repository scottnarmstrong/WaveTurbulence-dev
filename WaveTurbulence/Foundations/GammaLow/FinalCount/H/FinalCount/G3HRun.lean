/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3HRun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the combined invariant of a run with history**: `Good`, `HInv` (records), `HGap` (dart gaps). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

theorem RunInv.step1L {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hr : RunInv R L γ η w κ h) :
    RunInv R L γ η w κ h' :=
  ⟨hs.step.good hr.good, hs.inv hr.hrec, hs.gap hr.gap hr.good.1⟩

alias _root_.WaveTurbulence.FinalCountG3.RunInv.step1L := _root_.WaveTurbulence.GammaLow.FinalCount.H.RunInv.step1L

end WaveTurbulence.GammaLow.FinalCount.H

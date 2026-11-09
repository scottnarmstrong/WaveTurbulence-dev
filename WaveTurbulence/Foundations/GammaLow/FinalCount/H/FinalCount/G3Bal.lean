/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Bal`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: balance of the degree-`2` atoms.**  `BalM M`: degree bounds `≤ 2` and every atom of degree `2`
has one incoming and one outgoing bond.  Preserved by cuts and restrictions, hence along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

section bal
variable {D : Type*} [Fintype D] [DecidableEq D]

end bal

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

theorem Step1.bal {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') (hB : BalM s.M) : BalM s'.M := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    exact BalM.restrict ((hB.cut K.cut_a).cut K.cut_b) _ K.closed

theorem Run.bal {R : ℕ} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {sf : St.{u} V D₀}
    (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : BalM sf.M := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : BalM (St.init M₀).M := ⟨hS.bounds, fun a ha hd => by have := hS.deg3 a ha; have hd' : M₀.deg a = 2 := hd; omega⟩
  exact bal_rtg (fun _ _ h g => Step4.bal h g) h4 (bal_rtg (fun _ _ h g => Step3.bal h g) h3
    (bal_rtg (fun _ _ h g => Step2.bal h g) h2 (bal_rtg (fun _ _ h g => Step1.bal h g) h1 g0)))

end WaveTurbulence.GammaLow.FinalCount.H

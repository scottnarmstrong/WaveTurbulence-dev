/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3DPRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Range
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3DPRun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `HRun.dp`**, the dart-set invariant along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

theorem HRun.dp {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf) : DPInv hf := by
  obtain ⟨h₁, h₂, h₃, a1, _, a2, _, a3, _, a4, _⟩ := hr
  have r0 := AncRel.init M₀
  have i0 : DPInv (HSt.init M₀) := DPInv.init M₀
  have s1 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a1 i0 r0
  have s2 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a2 s1.1 s1.2
  have s3 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a3 s2.1 s2.2
  exact (rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a4 s3.1 s3.2).1

end WaveTurbulence.GammaLow.FinalCount.H

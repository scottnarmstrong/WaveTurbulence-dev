/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3N12`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: (N1) and (N2) of ruling R18**, from the cutting history of a run.

* (N1) every `β`-atom of `𝕄_fin` is the product of a cut with nonzero gap (DH23 L1985, TARGET `remtame`);
* (N2) if `κ_{v₁} = κ_{v₂} = 0` and `g_β = ±g₁ ± g₂` (the three gaps sum to zero), then
  `|g_β| ≥ L^{-50η} min(R₁,R₂)` (DH23 L1895: "by the definition of `(ι_v, κ_v)`"). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

theorem HRun.inv {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf) :
    HInv L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, a1, -, a2, -, a3, -, a4, -⟩ := hr
  exact rtg_inv (fun _ _ hs hI => hs.inv hI) a4 (rtg_inv (fun _ _ hs hI => hs.inv hI) a3
    (rtg_inv (fun _ _ hs hI => hs.inv hI) a2 (rtg_inv (fun _ _ hs hI => hs.inv hI) a1 (HInv.init M₀))))

end WaveTurbulence.GammaLow.FinalCount.H

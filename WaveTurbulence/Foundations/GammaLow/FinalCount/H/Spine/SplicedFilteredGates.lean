/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFilteredGates
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredCountA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SplicedFilteredGates`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal ladderl1old and finalcount1 compose to a bound for the actual fixed-choice kernel. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem spliced_filtered_bound_of_source_gates (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hC₁ : 0 < P.C₁)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (C : Src.CountingChoices Src.γL G P.d) (hhinges : D.hinges = C.subpro.hinges)
    (hgeom : Src.CountingGeometry G C) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (s : Set (GenDecoration G P.d roots 0))
    (hs : s ⊆ splicedSelectedCarrier G D C P.L P.γ P.η base roots) :
    ‖splicedFilteredKernel G D P.L P.γ P.η P.δ base roots s‖ₑ ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
        ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
          P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
        (ENNReal.ofReal
          (P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
            P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
          ENNReal.ofReal (molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁)) := by
  have hF := hfourier p hp R hR hRmax G hplain hirred hbal hn hnmax D C.ladderScale hlayer hD base roots
  have hC := hcount p hp R hR hRmax G hplain hirred hbal hn hnmax D C hhinges hgeom base roots
    (Src.splicedCountingAdmissible G D C P.L P.γ P.η base roots) (fun _ h => h)
  apply spliced_filtered_bound_of_countA G hplain D hD C hL hδ hC₁ P.γ P.η base roots s hs _ _ _ hC
  have hu : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) := by positivity
  rw [← ENNReal.ofReal_mul hu]
  exact hF

end WaveTurbulence.GammaLow.FinalCount.H

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3CompRun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: `CompBeta` along a whole run: every component of the final molecule contains a `β`-atom or
an atom of odd degree. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem Step1.compBeta {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hg : Good R s) (hC : CompBeta s) : CompBeta s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    by_cases hα : K.post.numComponents ≤ s.M.numComponents
    · have : alphaOrBeta K.post.numComponents s.M.numComponents R' kp = .alpha R' kp := by
        unfold alphaOrBeta; rw [if_pos hα]
      rw [this]; exact vine_compBeta_alpha K hg hC R' kp hu hl hα
    · have : alphaOrBeta K.post.numComponents s.M.numComponents R' kp = .beta := by
        unfold alphaOrBeta; rw [if_neg hα]
      rw [this]
      exact ((hC.cutβ K.cut_a .beta (Or.inl rfl)).cutβ K.cut_b .beta (Or.inl rfl)).delSt _ K.closed

end WaveTurbulence.GammaLow.FinalCount.H

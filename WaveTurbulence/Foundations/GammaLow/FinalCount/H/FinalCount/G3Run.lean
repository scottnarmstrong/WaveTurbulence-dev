/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Run`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: the invariants `Inv`, `Clean` along a run of the algorithm. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

theorem Step1.good {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hg : Good R s) : Good R s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents s.M.numComponents R' kp
    have hng := Cls.ne_ghost_of_isAB hab
    refine ⟨hg.1.vineStL K _ hab hu hl h3a h3b, ?_⟩
    exact ((hg.2.cutSt _ _ _ _ _ _ hng hng).cutSt _ _ _ _ _ _ hng hng).delSt _ _

end WaveTurbulence.GammaLow.FinalCount.H

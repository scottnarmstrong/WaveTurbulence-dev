/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3RelRun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: `DartRel` along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀}

theorem Step1.rel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hr : DartRel M₀ s) : DartRel M₀ s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents s.M.numComponents R' kp
    have hce := Cls.ne_eps_of_isAB hab
    have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ _ _ hce hce K.cut_a.2.1
    have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ _ _ hce hce K.cut_b.2.1
    exact h2.delSt _ K.closed

theorem Run.dartRel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {sf : St.{u} V D₀}
    (hr : Run L γ η w κ (St.init M₀) sf) : DartRel M₀ sf := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have r1 := rel_rtg (fun _ _ h g => Step1.rel h g) h1 (DartRel.init M₀)
  have r2 := rel_rtg (fun _ _ h g => Step2.rel h g) h2 r1
  have r3 := rel_rtg (fun _ _ h g => Step3.rel h g) h3 r2
  exact rel_rtg (fun _ _ h g => Step4.rel h g) h4 r3

end WaveTurbulence.GammaLow.FinalCount.H

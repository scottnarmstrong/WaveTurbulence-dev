/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 3**: the run invariant `InvL` with the index `R` as a RUN VARIABLE (no `Flat`, no `t`), its
initialisation for `SubHypL`, and its preservation by the old steps (index unchanged) and by `HStepD3` (index `R - 1`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

variable {h h' : HSt V D₀}

theorem InvL.step1H (hs : HStep1 L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) : InvL M₀ R L γ η w κ h' where
  good := hs.step.good hr.good
  hrec := hs.inv hr.hrec
  gap := hs.gap hr.gap hr.good.1
  comp := hs.step.compBeta hr.good hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

alias _root_.WaveTurbulence.FinalCountG3.InvL.step1H := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.step1H
theorem HStepD3.data {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') :
    ∃ v x₁ x₂, D3Data h v x₁ x₂ ∧ h' = h.betaPost v x₁ x₂ := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes => exact ⟨v, x₁, x₂, ⟨hv, hε, hd, hx₁, hx₂, hne, ho₁, ho₂⟩, rfl⟩

/-- **The index drops by one** along a degree-`2` cut. -/
theorem InvL.stepD3L {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    1 ≤ R ∧ InvL M₀ (R - 1) L γ η w κ h' := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    have hD : D3Data h v x₁ x₂ := ⟨hv, hε, hd, hx₁, hx₂, hne, ho₁, ho₂⟩
    obtain ⟨hR, hg⟩ := hr.good.betaSt hv hε hd
    exact ⟨hR, { good := hg
                 hrec := hr.hrec.betaPost hv hnz
                 gap := hr.gap.betaPost hD
                 comp := hr.comp.betaSt hε
                 bal := hr.bal.betaSt hd hx₁ hx₂ ho₁ ho₂
                 rel := hr.rel.betaSt v }⟩

alias _root_.WaveTurbulence.FinalCountG3.InvL.stepD3L := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.stepD3L
end WaveTurbulence.GammaLow.FinalCount.H

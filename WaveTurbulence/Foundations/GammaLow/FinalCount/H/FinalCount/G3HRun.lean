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
theorem HRun.runInv {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    RunInv R L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, a1, -, a2, -, a3, -, a4, -⟩ := hr
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → RunInv R L γ η w κ a → RunInv R L γ η w κ b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → RunInv R L γ η w κ a → RunInv R L γ η w κ b := by
    intro S hS a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih => exact hS _ _ hs ih
  exact key (fun _ _ hs hr => hr.step4 hs) a4 (key (fun _ _ hs hr => hr.step3 hs) a3
    (key (fun _ _ hs hr => hr.step2 hs) a2 (key (fun _ _ hs hr => hr.step1L hs) a1 (RunInv.init hS h0))))

end WaveTurbulence.GammaLow.FinalCount.H

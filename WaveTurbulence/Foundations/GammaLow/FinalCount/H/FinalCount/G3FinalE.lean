/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Bal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Final2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3FinalE`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the corrected `finalmol`** (TARGET Prop `finalmol`, L2182--L2190; errata E9).

`HRunE L γ η w κ h₀ hf t` is a run of Steps 1--4 in which the erase step `HStep5` (TARGET Remark `remtame` case (ii))
is interleaved with Steps 2 and 4; `t` is the number of erasures.  The Step-4 stopping condition is `NoBetaCutAll`:
no `ε`-atom of degree `≥ 3` allows a `β`-cut *of any gap* (a zero-gap cut is case (i) of Remark `remtame` and is not
part of this model: a zero-gap `β`-cuttable atom must be erased).  Final conclusions are in `G3FinalE2`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **A run with `t` tame-atom erasures** (TARGET Operations 1--4 with Remark `remtame` (ii)). -/
def HRunE (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h₀ hf : HSt V D₀) (t : ℕ) : Prop :=
  ∃ (h₁ h₂ h₃ : HSt V D₀) (t₂ : ℕ),
    Relation.ReflTransGen (HStep1 L γ η w κ) h₀ h₁ ∧ NoTripleBond h₁.s.M ∧
    Relation.ReflTransGen (StepE2 L γ η w κ) (0, h₁) (t₂, h₂) ∧ NoSGTriangle L γ η w κ h₂.s ∧
    Relation.ReflTransGen (HStep3 L γ η w κ) h₂ h₃ ∧ NoSGLeft L γ η w κ h₀.s h₃.s ∧
    Relation.ReflTransGen (StepE4 L w κ) (t₂, h₃) (t, hf) ∧ NoBetaCutAll hf.s

/-- All invariants hold along an erasure run. -/
theorem HRunE.inv {h₀ hf : HSt V D₀} {t : ℕ} (hr : HRunE L γ η w κ h₀ hf t) (h0 : InvE M₀ R 0 L γ η w κ h₀) :
    InvE M₀ R t L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, t₂, a1, -, a2, -, a3, -, a4, -⟩ := hr
  have i1 : InvE M₀ R 0 L γ η w κ h₁ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1L hs) a1 h0
  have i2 : InvE M₀ R t₂ L γ η w κ h₂ :=
    rtgE (P := fun t h => InvE M₀ R t L γ η w κ h) (fun t h t' h' hs hI => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact hI.step2 hs
      · exact hI.step5 hs) a2 i1
  have i3 : InvE M₀ R t₂ L γ η w κ h₃ :=
    rtgH (P := InvE M₀ R t₂ L γ η w κ) (fun _ _ hs hI => hI.step3 hs) a3 i2
  exact rtgE (P := fun t h => InvE M₀ R t L γ η w κ h) (fun t h t' h' hs hI => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact hI.step4 hs
      · exact hI.step5 hs) a4 i3

end WaveTurbulence.GammaLow.FinalCount.H

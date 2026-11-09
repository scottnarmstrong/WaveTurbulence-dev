/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3AdmRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3URun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: runs for an admissible class** (`UReach`) and their invariants.

`UReach … h` : `h` is reached from `HSt.init M₀` by uniform steps (`UStep1..4`).  `UCtx` bundles the invariants used by
the per-step estimates: `Good` (degree bounds, atom count), `AncRel`, `DartRel`, and the charge relation `AtomRelU`.
For every `κ ∈ Adm0` a `UReach` state is `HStep`-reachable (`UStepk.hstep`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀} {Rn : ℕ}

theorem UCtx.step1L {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStep1 L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  have hh := hs.hstep hk
  refine ⟨hh.step.good hc.good, hh.anc hc.anc, hh.step.rel hc.rel, ?_⟩
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b => exact hc.atom.step1L (hc.eps hp) K hu hl R kp

alias _root_.WaveTurbulence.FinalCountG3.UCtx.step1L := _root_.WaveTurbulence.GammaLow.FinalCount.H.UCtx.step1L
/-- One uniform step (any of Steps 1--4). -/
def UStepAny (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (h h' : HSt V D₀) : Prop :=
  UStep1 L γ η w Adm0 h h' ∨ UStep2 L γ η w Adm0 h h' ∨ UStep3 L γ η w Adm0 h h' ∨ UStep4 L w Adm0 h h'

/-- States reached from `M_sub` by uniform steps. -/
def UReach (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (M₀ : Molecule V D₀) (h : HSt V D₀) : Prop :=
  Relation.ReflTransGen (UStepAny L γ η w Adm0) (HSt.init M₀) h

theorem UCtx.step_anyL {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStepAny L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  rcases hs with hs | hs | hs | hs
  exacts [hc.step1L hk hs hp, hc.step2 hk hs hp, hc.step3 hk hs hp, hc.step4 hk hs hp]

alias _root_.WaveTurbulence.FinalCountG3.UCtx.step_anyL := _root_.WaveTurbulence.GammaLow.FinalCount.H.UCtx.step_anyL
theorem UReach.ctx {h : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hS : SubHyp Rn M₀)
    (hp : PinnedM0 Adm0 L w M₀) (hr : UReach L γ η w Adm0 M₀ h) : UCtx M₀ Rn Adm0 L w h := by
  induction hr with
  | refl => exact UCtx.init hS
  | tail _ hs ih => exact ih.step_anyL hk hs hp

end WaveTurbulence.GammaLow.FinalCount.H

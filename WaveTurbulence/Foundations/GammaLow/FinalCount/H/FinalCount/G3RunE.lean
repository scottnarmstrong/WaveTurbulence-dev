/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3RunE`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: runs with tame-atom erasures** (`HRunE`) and their invariants.

TARGET Remark `remtame` (L2152): a ZG tame atom `v₃` of Operation 2 or `v` of Operation 4 is either cut with a zero
gap (case (i), the model's `HStep2`/`HStep4` allow `pgap = 0` only through the cases below) or *erased* (case (ii),
`HStep5`).  `HRunE … t` is the run in which `HStep5` is interleaved with Steps 2 and 4; `t` counts the erasures.
The invariant `Good` holds with `R + 2 t` (each erasure raises `4V - 2E - 2(V_α + V_β)` by `4`). -/
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

/-! ### Balance of the steps -/

theorem Step1.balS {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') (hB : BalS s) : BalS s' := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    exact ((hB.cutSt K.cut_a _ _).cutSt K.cut_b _ _).delSt _ K.closed

/-! ### The combined invariant -/

variable {t : ℕ} {h h' : HSt V D₀}

theorem InvE.step1L (hs : HStep1 L γ η w κ h h') (hr : InvE M₀ R t L γ η w κ h) : InvE M₀ R t L γ η w κ h' where
  good0 := fun ht => hs.step.good (hr.good0 ht)
  good := by obtain ⟨R', hR', hg⟩ := hr.good; exact ⟨R', hR', hs.step.good hg⟩
  hrec := hs.inv hr.hrec
  gap := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.gap hr.gap hg.1
  flat := fun ht => hs.step.flat (hr.flat ht)
  comp := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.step.compBeta hg hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

alias _root_.WaveTurbulence.FinalCountG3.InvE.step1L := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvE.step1L
end WaveTurbulence.GammaLow.FinalCount.H

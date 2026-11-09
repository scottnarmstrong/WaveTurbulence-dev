/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Flat`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the flatness invariant** `Flat s` (`contrib ≤ 1` at every atom).

It carries the *erasure-free* strengthening of `Inv`: in a state without tame-atom erasures (TARGET Remark `remtame`,
case (ii)) the `ε`-atoms have degree `≥ 3` and there are exactly `2R` atoms of odd degree.  (After an erasure the
neighbours of the erased atom can have defect `≥ 2`.) -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

section
variable {s : St.{u} V D₀} {R : ℕ}

theorem Flat.vineStL (hF : Flat s) (K : Step1.VineCut Src.γL s.M) (c : Cls) (hc : c.IsAB)
    (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps) : Flat (vineSt s K c) := by
  have hc2 := Cls.base_eq_two hc
  have hF1 := hF.cutSt K.cut_a c c (by rw [hu, hc2]; rfl) hc2
  have hlow : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cls K.C.lower = .eps := by
    show Function.update (Function.update s.cls K.C.upper c) K.fa c K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]; exact hl
  have hF2 := hF1.cutSt K.cut_b c c (by rw [hlow, hc2]; rfl) hc2
  exact hF2.delSt _ K.closed

alias _root_.WaveTurbulence.FinalCountG3.Flat.vineStL := _root_.WaveTurbulence.GammaLow.FinalCount.H.Flat.vineStL
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s' : St.{u} V D₀}

theorem Step1.flat (h : Step1 L γ η w κ s s') (hF : Flat s) : Flat s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    exact hF.vineStL K _ (alphaOrBeta_isAB _ _ _ _) hu hl

end
end WaveTurbulence.GammaLow.FinalCount.H

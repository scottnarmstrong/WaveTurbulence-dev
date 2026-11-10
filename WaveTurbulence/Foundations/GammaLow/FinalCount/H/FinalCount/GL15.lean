/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL15
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Ex1New
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL15`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 15**: the uniform step `UStepD1` and its deviation `UStepD1.excess_new` (`excessprop1 (2)` with a
degree-`2` joint: a new component is created, `ΔF = 1`, `ΔV_β = 2`, TARGET-literal bookkeeping with the isolated halves kept; deleting
them is a dartless restriction, deviation `1`; the true increments are smaller and the assembly pays with the index drop).
`UStepD1.excess_new` is a modification of `UStep1.excess_new` (G3Ex1New, sha256 in COPIED-SHA256SUMS) whose proof body is copied. 

Low-range change (L6-HLOW, as H-G3's `UStep1.excess_new` in G3Ex1New): `UStepD1.excess_new` has no `VINEPARAM`
binder (L4's Theorem C is proved: `TVine.Chart.tvineChartExists_holds`), and the removed single vine is a member of
the low family (`Step1.SingleVineVCGamma K`); proof = L6-STEP1's `prop94_vine_newcomp` at `Src.γL` with
`Step1.singleVineVC_of_gamma`.-/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

section iso
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

end iso

variable {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {M₀ : Molecule V D₀}

inductive UStepD1 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) :
    HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2)
      (htwin : ∀ k0, Adm0 k0 → (pgap L w k0 (h.s.pr K.y₁ K.y₂) = pgap L w k0 (h.s.pr K.x₁ K.x₂) ∨
        pgap L w k0 (h.s.pr K.y₁ K.y₂) = -pgap L w k0 (h.s.pr K.x₁ K.x₂)))
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hnew : h.s.M.numComponents < K.post.numComponents)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      UStepD1 C L γ η w Adm0 h (h.vinePostGL K)

theorem UStepD1.hstep {C : CollData M₀} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : UStepD1 C L γ η w Adm0 h h') (hk : Adm0 κ) : HStepD1 C L γ η w κ h h' := by
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl => exact HStepD1.vine h K hu hl hd2 (htwin κ hk) (hsg κ hk) hnew hdu hdl

variable {d : ℕ}

end WaveTurbulence.GammaLow.FinalCount.H

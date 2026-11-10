/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1Dev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Pot
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmP1Dev`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1 (c): `stepRHS` of a vine removal** in the two cases of `excessprop1` ((1) no new component, (2) one new component). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem vinePost_s (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePostL K R kp).s = vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp) := rfl

theorem vinePost_numComponents (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePostL K R kp).s.M.numComponents = K.post.numComponents := rfl

theorem stepRHS_vine_alpha {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (hap : ApPos h.s) (K : Step1.VineCut Src.γL h.s.M) {R : ℝ} {kp : ℕ}
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hF : K.post.numComponents ≤ h.s.M.numComponents) :
    stepRHS L γ η h (h.vinePostL K R kp) = excessRHS L γ η [(R, kp), (R, kp)] 0 0 := by
  have hc : alphaOrBeta K.post.numComponents h.s.M.numComponents R kp = Cls.alpha R kp := by
    unfold alphaOrBeta; rw [if_pos hF]
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hA := apProd_vineSt L γ η h.s K (Cls.alpha R kp) hrem
  have hB := vBeta_vineSt h.s K (Cls.alpha R kp) hrem
  have hFF : K.post.numComponents = h.s.M.numComponents := le_antisymm hF (vine_F_ge K)
  unfold stepRHS
  have hFp : (vineSt h.s K (Cls.alpha R kp)).M.numComponents = h.s.M.numComponents := hFF
  rw [vinePost_s, hc, hA, hB, hFp]
  rw [excessRHS_alpha]
  simp only [apFactor, if_neg (by simp : Cls.alpha R kp ≠ Cls.beta), sub_self, mul_zero, add_zero, Nat.cast_add, Real.rpow_zero,
    mul_one, add_sub_cancel_left]
  field_simp

theorem stepRHS_vine_new {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (hap : ApPos h.s) (K : Step1.VineCut Src.γL h.s.M) {R : ℝ} {kp : ℕ}
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hF : K.post.numComponents = h.s.M.numComponents + 1) :
    stepRHS L γ η h (h.vinePostL K R kp) = excessRHS L γ η [] 1 2 := by
  have hc : alphaOrBeta K.post.numComponents h.s.M.numComponents R kp = Cls.beta := by
    unfold alphaOrBeta; rw [if_neg (by omega)]
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hA := apProd_vineSt L γ η h.s K Cls.beta hrem
  have hB := vBeta_vineSt h.s K Cls.beta hrem
  refine stepRHS_beta hL hAp ?_ ?_ ?_
  · rw [vinePost_numComponents]; exact hF
  · rw [vinePost_s, hc, hB]; simp
  · rw [vinePost_s, hc, hA]; simp [apFactor]

end WaveTurbulence.GammaLow.FinalCount.H

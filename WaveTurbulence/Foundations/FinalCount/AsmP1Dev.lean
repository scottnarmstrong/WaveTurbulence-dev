/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1Pot
public import WaveTurbulence.Foundations.FinalCount.AsmPot
public import WaveTurbulence.Foundations.FinalCount.VCNew13
/-! **FINALCOUNT-ASSEMBLY, phase 1 (c): `stepRHS` of a vine removal** in the two cases of `excessprop1` ((1) no new component, (2) one new component). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem vinePost_s (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePost K R kp).s = vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp) := rfl

theorem vinePost_numComponents (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePost K R kp).s.M.numComponents = K.post.numComponents := rfl

theorem stepRHS_vine_alpha {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (hap : ApPos h.s) (K : VineCut h.s.M) {R : ℝ} {kp : ℕ}
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hF : K.post.numComponents ≤ h.s.M.numComponents) :
    stepRHS L γ η h (h.vinePost K R kp) = excessRHS L γ η [(R, kp), (R, kp)] 0 0 := by
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

theorem stepRHS_vine_new {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (hap : ApPos h.s) (K : VineCut h.s.M) {R : ℝ} {kp : ℕ}
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hF : K.post.numComponents = h.s.M.numComponents + 1) :
    stepRHS L γ η h (h.vinePost K R kp) = excessRHS L γ η [] 1 2 := by
  have hc : alphaOrBeta K.post.numComponents h.s.M.numComponents R kp = Cls.beta := by
    unfold alphaOrBeta; rw [if_neg (by omega)]
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hA := apProd_vineSt L γ η h.s K Cls.beta hrem
  have hB := vBeta_vineSt h.s K Cls.beta hrem
  refine stepRHS_beta hL hAp ?_ ?_ ?_
  · rw [vinePost_numComponents]; exact hF
  · rw [vinePost_s, hc, hB]; simp
  · rw [vinePost_s, hc, hA]; simp [apFactor]

theorem excessRHS2_vine {L γ η : ℝ} (hL : 0 < L) :
    WaveTurbulence.VineCount.excessRHS2 L γ η [] 1 2 = L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2 := WaveTurbulence.VineCount.excessRHS2_eq L γ η [] 1 2 hL

end WaveTurbulence.FinalCountAsm

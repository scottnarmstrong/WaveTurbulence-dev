/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1H
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmP1H`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1: the per-step inequality `hW1` of the potential.**  The phase-1 exponent is
`g₁ = gExp - γ₀ (F_max - F(h))`: a vine removal creating a component costs `L^{γ₀}` (excessprop1 (2)), refunded by the `F`-term;
`g₁ = gExp + γ₀ (F - F_max)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hW1_of [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {L γ η : ℝ} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ}
    (hY0 : 0 ≤ Y0) (crit : V → Prop) (Fmax : ℝ) {CA CN : ℝ} (hCA : 0 ≤ CA) (hCN : 0 ≤ CN) (N : ℕ)
    (hNC : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    {h : HSt V D₀} {t : T1 h} (hap : ApPos h.s) (hI : Inv Rn h.s) (hn : Node1 C crit L γ η h t) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) *
      WPot L γ η Y0 (g1 γ η crit Fmax) (post1 C crit L γ η h t)) ≤ WPot L γ η Y0 (g1 γ η crit Fmax) h := by
  have hL : 0 < L := by linarith
  obtain ⟨K, F, hK⟩ := node1_spec hn
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ t.2.2.2.2.1 := zpow_pos (by norm_num) _
  set R : ℝ := (2 : ℝ) ^ t.2.2.2.2.1 with hRdef
  set kp : ℕ := (if t.2.2.2.2.2.1 then 50 else 0) with hkpdef
  set c := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hcdef
  have hcne : c ≠ .eps := by rw [hcdef]; unfold alphaOrBeta; split_ifs <;> simp
  have hcpos : ∀ R' kp', c = .alpha R' kp' → 0 < R' := by
    intro R' kp' hc
    rw [hcdef] at hc; unfold alphaOrBeta at hc
    split_ifs at hc
    · cases hc; exact hRpos
  have hap' : ApPos (h.vinePostL K R kp).s := by rw [vinePost_s]; exact apPos_vineSt hap K c hcpos
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hAp' := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
  have hrho : h.s.M.rho ≤ (h.vinePostL K R kp).s.M.rho + 86 := F.hrho
  have hcrit : critCount crit h.s ≤ critCount crit (h.vinePostL K R kp).s + 2 := by
    rw [vinePost_s]; exact critCount_vineSt crit h.s K c hcne F.hint
  have hgd := gExp_drop hη crit (h := h) (h' := h.vinePostL K R kp) (a := 86) (b := 2) hrho hcrit
  rw [hK]
  unfold vCost
  have hFle := vine_F_le_succ K
  by_cases hF : (h.vinePostL K R kp).s.M.numComponents ≤ h.s.M.numComponents
  · rw [if_pos hF]
    have hF' : (h.vinePostL K R kp).s.M.numComponents = h.s.M.numComponents := le_antisymm hF (vine_F_ge K)
    refine hW_generic hL1 hAp hAp' hY0 (g1 γ η crit Fmax) (δg := 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) ?_ CA hCA N
      (le_trans (by gcongr; exact le_max_left _ _) hNC)
    unfold g1
    rw [hF']
    linarith
  · rw [if_neg hF]
    have hF1 : (h.vinePostL K R kp).s.M.numComponents = h.s.M.numComponents + 1 := le_antisymm hFle (by omega)
    refine hW_generic hL1 hAp hAp' hY0 (g1 γ η crit Fmax)
      (δg := 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) - min γ (1 - γ)) ?_ (CN * L ^ (min γ (1 - γ))) (by positivity) N ?_
    · unfold g1
      rw [hF1]; simp only [Nat.cast_add, Nat.cast_one]
      linarith
    · have : L ^ (η ^ 3 - (4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) - min γ (1 - γ))) =
          L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) * L ^ (min γ (1 - γ)) := by
        rw [← Real.rpow_add hL]; congr 1; ring
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_trans (by gcongr; exact le_max_right _ _) hNC) (by positivity)

end WaveTurbulence.GammaLow.FinalCount.H

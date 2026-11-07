/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1d
/-! **FINALCOUNT-ASSEMBLY, phase 1: the per-step inequality `hW1` of the potential.**  The phase-1 exponent is
`g₁ = gExp - γ₀ (F_max - F(h))`: a vine removal creating a component costs `L^{γ₀}` (excessprop1 (2)), refunded by the `F`-term;
`g₁ = gExp + γ₀ (F - F_max)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The exponent of the phase-1 potential. -/
noncomputable def g1 (γ η : ℝ) (crit : V → Prop) (Fmax : ℝ) (h : HSt V D₀) : ℝ :=
  gExp η crit h - min γ (1 - γ) * (Fmax - (h.s.M.numComponents : ℝ))

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
  have hap' : ApPos (h.vinePost K R kp).s := by rw [vinePost_s]; exact apPos_vineSt hap K c hcpos
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hAp' := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
  have hrho : h.s.M.rho ≤ (h.vinePost K R kp).s.M.rho + 86 := F.hrho
  have hcrit : critCount crit h.s ≤ critCount crit (h.vinePost K R kp).s + 2 := by
    rw [vinePost_s]; exact critCount_vineSt crit h.s K c hcne F.hint
  have hgd := gExp_drop hη crit (h := h) (h' := h.vinePost K R kp) (a := 86) (b := 2) hrho hcrit
  rw [hK]
  unfold vCost
  have hFle := vine_F_le_succ K
  by_cases hF : (h.vinePost K R kp).s.M.numComponents ≤ h.s.M.numComponents
  · rw [if_pos hF]
    have hF' : (h.vinePost K R kp).s.M.numComponents = h.s.M.numComponents := le_antisymm hF (vine_F_ge K)
    refine hW_generic hL1 hAp hAp' hY0 (g1 γ η crit Fmax) (δg := 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) ?_ CA hCA N
      (le_trans (by gcongr; exact le_max_left _ _) hNC)
    unfold g1
    rw [hF']
    linarith
  · rw [if_neg hF]
    have hF1 : (h.vinePost K R kp).s.M.numComponents = h.s.M.numComponents + 1 := le_antisymm hFle (by omega)
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

theorem cut_F_ge {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}
    (hc : M.IsCutData v v₂ x₁ x₂) : M.numComponents ≤ (M.cut v v₂ x₁ x₂).numComponents := by
  by_cases hα : M.IsAlphaCut v v₂ x₁ x₂
  · exact (numComponents_cut_of_same M hc ((isAlphaCut_iff M hc).1 hα)).ge
  · rw [numComponents_cut_of_not_same M hc (fun hs => hα ((isAlphaCut_iff M hc).2 hs))]; omega

/-- A triple cut in phase 1 (an `α`/`β` cut, `UStep3`): the `F`-term of `g₁` does not hurt. -/
theorem hW3_1 {Rn : ℕ} {L γ η : ℝ} {w : Mom d} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ} (hY0 : 0 ≤ Y0) (crit : V → Prop) (Fmax K : ℝ) (hγ0 : 0 ≤ min γ (1 - γ))
    (hK : 0 ≤ K) (N : ℕ) (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hap : ApPos h.s) (hI : Inv Rn h.s) (hs : UStep3 L γ η w Adm0 h h') :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η Y0 (g1 γ η crit Fmax) h') ≤
      WPot L γ η Y0 (g1 γ η crit Fmax) h := by
  have hL : 0 < L := by linarith
  have hap' := apPos_cut3 hs hap
  have hl : h.s.M.rho ≤ h'.s.M.rho + 1 ∧ critCount crit h.s ≤ critCount crit h'.s + 1 ∧
      h.s.M.numComponents ≤ h'.s.M.numComponents := by
    cases hs with
    | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 =>
      have h1 := cut_loss hI crit hc (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R kp else Cls.beta)
        (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R kp else Cls.beta)
      exact ⟨h1.1, h1.2, cut_F_ge h.s.M hc⟩
  have hgd := gExp_drop hη crit (h := h) (h' := h') (a := 1) (b := 1) hl.1 hl.2.1
  refine hW_generic hL1 (apProd_pos hL hap) (apProd_pos hL hap') hY0 (g1 γ η crit Fmax)
    (δg := 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) ?_ K hK N hNC
  unfold g1
  have : (h.s.M.numComponents : ℝ) ≤ h'.s.M.numComponents := by exact_mod_cast hl.2.2
  nlinarith

end WaveTurbulence.FinalCountAsm

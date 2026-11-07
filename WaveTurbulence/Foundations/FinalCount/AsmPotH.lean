/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmRho3
/-! **FINALCOUNT-ASSEMBLY: the `hW` hypotheses of the phase cover theorems 2, 3, 4** from `hW_generic`.
The constants `N · K ≤ L^{η³ - δg}` are the (polylog absorption) hypotheses `hNC`. -/
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

theorem apPos_cut3 {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hs : UStep3 L γ η w Adm0 h h')
    (hap : ApPos h.s) : ApPos h'.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 =>
    obtain ⟨⟨z, rfl⟩, -, -⟩ := hR
    have hRpos : (0 : ℝ) < (2 : ℝ) ^ z := zpow_pos (by norm_num) z
    by_cases hα : h.s.M.IsAlphaCut v v₂ x₁ x₂
    · have : (h.cut3Post v v₂ x₁ x₂ ((2 : ℝ) ^ z) kp).s = h.s.cutSt v v₂ x₁ x₂ (.alpha ((2 : ℝ) ^ z) kp) (.alpha ((2 : ℝ) ^ z) kp) := by
        simp [HSt.cut3Post, if_pos hα]
      rw [this]; exact apPos_cutSt_alpha h.s hap hRpos _
    · have : (h.cut3Post v v₂ x₁ x₂ ((2 : ℝ) ^ z) kp).s = h.s.cutSt v v₂ x₁ x₂ .beta .beta := by
        simp [HSt.cut3Post, if_neg hα]
      rw [this]; exact apPos_cutSt_beta h.s hap

theorem apPos_cut4 {L : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hs : UStep4 L w Adm0 h h')
    (hap : ApPos h.s) : ApPos h'.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact apPos_cutSt_beta h.s hap

theorem apPos_step2 {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hs : UStep2 L γ η w Adm0 h h')
    (hap : ApPos h.s) : ApPos h'.s := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 =>
    refine apPos_triSt hap T Q kp (fun j => ?_) hcl
    obtain ⟨⟨z, hz⟩, -, -⟩ := hQ j
    rw [hz]; exact zpow_pos (by norm_num) z

/-- Loss of a single cut (Steps 3, 4): `ρ` and `critCount` drop by at most `1` each. -/
theorem cut_loss {Rn : ℕ} {h : HSt V D₀} (hI : Inv Rn h.s) (crit : V → Prop) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hc : h.s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) :
    h.s.M.rho ≤ (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.rho + 1 ∧
      critCount crit h.s ≤ critCount crit (h.s.cutSt v v₂ x₁ x₂ c₁ c₂) + 1 :=
  ⟨rho_le_cut h.s.M hc (fun a ha => deg_le_four _ (hI.bounds a ha)), critCount_cutSt crit h.s hc c₁ c₂⟩

theorem gExp_drop {η : ℝ} (hη : 0 ≤ η) (crit : V → Prop) {h h' : HSt V D₀} {a b : ℕ}
    (hρ : h.s.M.rho ≤ h'.s.M.rho + a) (hk : critCount crit h.s ≤ critCount crit h'.s + b) :
    gExp η crit h - 4 * η ^ 6 * ((a : ℝ) + b) ≤ gExp η crit h' := by
  unfold gExp
  have h1 : (h.s.M.rho : ℝ) ≤ h'.s.M.rho + a := by exact_mod_cast hρ
  have h2 : (critCount crit h.s : ℝ) ≤ critCount crit h'.s + b := by exact_mod_cast hk
  have : 0 ≤ 4 * η ^ 6 := by positivity
  nlinarith


/-- **`hW` from a loss bound.** -/
theorem hW_of_loss {L γ η : ℝ} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ} (hY0 : 0 ≤ Y0) (crit : V → Prop) {h h' : HSt V D₀}
    (hap : ApPos h.s) (hap' : ApPos h'.s) {a b : ℕ} (hρ : h.s.M.rho ≤ h'.s.M.rho + a)
    (hk : critCount crit h.s ≤ critCount crit h'.s + b) (K : ℝ) (hK : 0 ≤ K) (N : ℕ)
    (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * ((a : ℝ) + b))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η Y0 (gExp η crit) h') ≤
      WPot L γ η Y0 (gExp η crit) h := by
  have hL : 0 < L := by linarith
  exact hW_generic hL1 (apProd_pos hL hap) (apProd_pos hL hap') hY0 (gExp η crit) (gExp_drop hη crit hρ hk) K hK N hNC

theorem hW3 {Rn : ℕ} {L γ η : ℝ} {w : Mom d} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ} (hY0 : 0 ≤ Y0) (crit : V → Prop) (K : ℝ)
    (hK : 0 ≤ K) (N : ℕ) (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hap : ApPos h.s) (hI : Inv Rn h.s) (hs : UStep3 L γ η w Adm0 h h') :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η Y0 (gExp η crit) h') ≤
      WPot L γ η Y0 (gExp η crit) h := by
  have hap' := apPos_cut3 hs hap
  have hl : h.s.M.rho ≤ h'.s.M.rho + 1 ∧ critCount crit h.s ≤ critCount crit h'.s + 1 := by
    cases hs with
    | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 => exact cut_loss hI crit hc _ _
  exact hW_of_loss hL1 hη hY0 crit hap hap' hl.1 hl.2 K hK N hNC

theorem hW4 {Rn : ℕ} {L η : ℝ} {w : Mom d} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ} (hY0 : 0 ≤ Y0) (crit : V → Prop) (K : ℝ)
    (hK : 0 ≤ K) (N : ℕ) (γ : ℝ) (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hap : ApPos h.s) (hI : Inv Rn h.s) (hs : UStep4 L w Adm0 h h') :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η Y0 (gExp η crit) h') ≤
      WPot L γ η Y0 (gExp η crit) h := by
  have hap' := apPos_cut4 hs hap
  have hl : h.s.M.rho ≤ h'.s.M.rho + 1 ∧ critCount crit h.s ≤ critCount crit h'.s + 1 := by
    cases hs with
    | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact cut_loss hI crit hc _ _
  exact hW_of_loss hL1 hη hY0 crit hap hap' hl.1 hl.2 K hK N hNC

theorem hW2 {Rn : ℕ} {L γ η : ℝ} {w : Mom d} (hL1 : 1 ≤ L) (hη : 0 ≤ η) {Y0 : ℝ} (hY0 : 0 ≤ Y0) (crit : V → Prop) (K : ℝ)
    (hK : 0 ≤ K) (N : ℕ) (hNC : (N : ℝ) * K ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h h' : HSt V D₀} (hap : ApPos h.s) (hI : Inv Rn h.s) (hs : UStep2 L γ η w Adm0 h h') :
    (N : ℝ≥0∞) * (ENNReal.ofReal (K * stepRHS L γ η h h') * WPot L γ η Y0 (gExp η crit) h') ≤
      WPot L γ η Y0 (gExp η crit) h := by
  have hap' := apPos_step2 hs hap
  have hl : h.s.M.rho ≤ h'.s.M.rho + 9 ∧ critCount crit h.s ≤ critCount crit h'.s + 3 := by
    cases hs with
    | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 =>
      exact ⟨rho_tri_le T (fun a ha => deg_le_four _ (hI.bounds a ha)) Q kp hcl, critCount_triSt crit T Q kp hcl⟩
  exact hW_of_loss hL1 hη hY0 crit hap hap' hl.1 hl.2 K hK N hNC

end WaveTurbulence.FinalCountAsm

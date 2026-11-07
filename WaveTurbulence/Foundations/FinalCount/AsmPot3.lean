/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase4b
/-! **FINALCOUNT-ASSEMBLY, phase 3: the potential bookkeeping of an `SG` cut** (`α`-cut: `ΔF = ΔVβ = 0`, two new `α` factors;
`β`-cut: as phase 4) and the step deviation in `stepRHS` form with the explicit constant `max cα cβ`. -/
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

theorem vBeta_cutSt_alpha (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hc : s.M.IsCutData v v₂ x₁ x₂)
    (hε : s.cls v = .eps) (R : ℝ) (kp : ℕ) : vBeta (s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) = vBeta s := by
  obtain ⟨hv, hv₂, -⟩ := hc
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  unfold vBeta
  rw [cutSt_atoms, cutSt_cls]
  have e : (insert v₂ s.M.atoms).filter (fun a => Function.update (Function.update s.cls v (Cls.alpha R kp)) v₂ (Cls.alpha R kp) a = .beta) =
      s.M.atoms.filter (fun a => s.cls a = .beta) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases h1 : a = v₂
    · subst h1; simp [hv₂]
    · by_cases h2 : a = v
      · subst h2; simp [h1, hε]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, h1]
  rw [e]

theorem apProd_cutSt_alpha (s : St.{u} V D₀) (L γ η : ℝ) {v v₂ : V} {x₁ x₂ : s.D} (hc : s.M.IsCutData v v₂ x₁ x₂)
    (hε : s.cls v = .eps) (R : ℝ) (kp : ℕ) :
    apProd L γ η (s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) = apProd L γ η s * apFactor L γ η (.alpha R kp) ^ 2 := by
  obtain ⟨hv, hv₂, -⟩ := hc
  have h1 : v ≠ v₂ := fun e => hv₂ (e ▸ hv)
  unfold apProd
  rw [cutSt_atoms, cutSt_cls, Finset.prod_insert hv₂, ← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase s.M.atoms _ hv]
  have hne : ∀ a ∈ s.M.atoms.erase v, Function.update (Function.update s.cls v (Cls.alpha R kp)) v₂ (Cls.alpha R kp) a = s.cls a := by
    intro a ha
    have h1 : a ≠ v₂ := fun e => hv₂ (e ▸ Finset.mem_of_mem_erase ha)
    rw [Function.update_of_ne h1, Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [Finset.prod_congr rfl fun a ha => by rw [hne a ha]]
  rw [Function.update_self, Function.update_of_ne h1, Function.update_self, hε]
  simp only [apFactor]; ring

theorem apPos_cutSt_alpha (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hs : ApPos s) {R : ℝ} (hR : 0 < R) (kp : ℕ) :
    ApPos (s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) := by
  intro a ha R' kp' hcl
  rw [cutSt_atoms] at ha
  rw [cutSt_cls] at hcl
  by_cases h1 : a = v₂
  · subst h1; simp at hcl; exact hcl.1 ▸ hR
  · by_cases h2 : a = v
    · subst h2; simp [Function.update_of_ne h1] at hcl; exact hcl.1 ▸ hR
    · rw [Function.update_of_ne h1, Function.update_of_ne h2] at hcl
      exact hs a ((Finset.mem_insert.1 ha).resolve_left h1) R' kp' hcl

theorem stepRHS_alpha {L γ η : ℝ} (hL : 0 < L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s) {R : ℝ} {kp : ℕ}
    (hF : h'.s.M.numComponents = h.s.M.numComponents) (hB : vBeta h'.s = vBeta h.s)
    (hA : apProd L γ η h'.s = apProd L γ η h.s * apFactor L γ η (.alpha R kp) ^ 2) :
    stepRHS L γ η h h' = excessRHS L γ η [(R, kp), (R, kp)] 0 0 := by
  unfold stepRHS
  rw [hF, hB, hA, mul_div_cancel_left₀ _ hAp.ne', excessRHS_alpha]
  simp only [sub_self, mul_zero, Real.rpow_zero, mul_one, apFactor]

/-- The explicit constant of an `α`-cut. -/
noncomputable def cAlpha (d : ℕ) (γ η : ℝ) : ℝ := 26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)

/-- **Step 3 in potential form**: the deviation of the counts is bounded by `max cα cβ` times `stepRHS`. -/
theorem UStep3.dev_pot {L γ η δ C₁ : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} (H : TriReal d L γ η δ C₁)
    {Rn : ℕ} {h h' : HSt V D₀} (hs : UStep3 L γ η w Adm0 h h') (hI : Inv Rn h.s) (hAR : AtomRelU Adm0 L w h)
    (hAp : 0 < apProd L γ η h.s) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ h'.s.M.maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) :
    IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
      (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h')) := by
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 =>
    have key := cut_excess H hI hAR P hP0 hc hPinh R kp hR hkp hsim hι c hn
    by_cases hα : h.s.M.IsAlphaCut v v₂ x₁ x₂
    · have hs' : (h.cut3Post v v₂ x₁ x₂ R kp).s = h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp) := by
        simp [HSt.cut3Post, if_pos hα]
      have hF : (h.cut3Post v v₂ x₁ x₂ R kp).s.M.numComponents = h.s.M.numComponents :=
        numComponents_cut_of_same h.s.M hc ((isAlphaCut_iff h.s.M hc).1 hα)
      have hB : vBeta (h.cut3Post v v₂ x₁ x₂ R kp).s = vBeta h.s := by rw [hs']; exact vBeta_cutSt_alpha h.s hc hε R kp
      have hA : apProd L γ η (h.cut3Post v v₂ x₁ x₂ R kp).s = apProd L γ η h.s * apFactor L γ η (.alpha R kp) ^ 2 := by
        rw [hs']; exact apProd_cutSt_alpha h.s L γ η hc hε R kp
      rw [stepRHS_alpha hL hAp hF hB hA]
      have hX : 0 ≤ excessRHS L γ η [(R, kp), (R, kp)] 0 0 := by
        rw [excessRHS_alpha]; positivity
      exact isDeviation_mono (key.1 hα) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hX))
    · have hs' : (h.cut3Post v v₂ x₁ x₂ R kp).s = h.s.cutSt v v₂ x₁ x₂ .beta .beta := by
        simp [HSt.cut3Post, if_neg hα]
      have hF : (h.cut3Post v v₂ x₁ x₂ R kp).s.M.numComponents = h.s.M.numComponents + 1 :=
        numComponents_cut_of_not_same h.s.M hc (fun hs => hα ((isAlphaCut_iff h.s.M hc).2 hs))
      have hB : vBeta (h.cut3Post v v₂ x₁ x₂ R kp).s = vBeta h.s + 2 := by rw [hs']; exact vBeta_cutSt_beta h.s hc hε
      have hA : apProd L γ η (h.cut3Post v v₂ x₁ x₂ R kp).s = apProd L γ η h.s := by
        rw [hs']; exact apProd_cutSt_beta h.s L γ η hc hε
      rw [stepRHS_beta hL hAp hF hB hA]
      have hX : 0 ≤ excessRHS L γ η [] 1 2 := by rw [excessRHS_beta L γ η hL]; positivity
      exact isDeviation_mono (key.2 hα) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hX))

end WaveTurbulence.FinalCountAsm

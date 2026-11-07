/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM06
public import WaveTurbulence.Foundations.FinalCount.G3CutRestrict
/-! **FINALCOUNT-G3: `FinalDec` for a component** (fourth part: the `ι/κ` property (N2) at the level of darts). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

theorem pm_mul3L {a b c : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    a * b * c = 1 ∨ a * b * c = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

theorem pm_smul_casesL {g r : Mom d} (h : r = g ∨ r = -g) : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ r = e • g := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩

section dec4
variable (hC : Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm)
include hC

theorem dec_iotaL (hL : 1 ≤ L) (hη : 0 ≤ η) {v₁ v₂ v₃ : V} (h1 : v₁ ∈ hf.s.M.atoms) (h2 : v₂ ∈ hf.s.M.atoms)
    (h3 : v₃ ∈ hf.s.M.atoms) (hα1 : (toCls (hf.s.cls v₁)).IsAlpha) (hα2 : (toCls (hf.s.cls v₂)).IsAlpha)
    (hβ : (toCls (hf.s.cls v₃)).IsBeta) (hk : (toCls (hf.s.cls v₁)).kap + (toCls (hf.s.cls v₂)).kap = 0)
    {x₁ y₁ x₂ y₂ x₃ y₃ : hf.s.D} (hx₁ : hf.s.M.atom x₁ = v₁) (hy₁ : hf.s.M.atom y₁ = v₁) (hn₁ : x₁ ≠ y₁)
    (hx₂ : hf.s.M.atom x₂ = v₂) (hy₂ : hf.s.M.atom y₂ = v₂) (hn₂ : x₂ ≠ y₂)
    (hx₃ : hf.s.M.atom x₃ = v₃) (hy₃ : hf.s.M.atom y₃ = v₃) (hn₃ : x₃ ≠ y₃)
    (hsum : ∃ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x₃ y₃ =
        s₁ • Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x₁ y₁ + s₂ • Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x₂ y₂) :
    L ^ (-50 * η) * min (toCls (hf.s.cls v₁)).lab (toCls (hf.s.cls v₂)).lab / 2 ≤
      ‖Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x₃ y₃‖ := by
  obtain ⟨ρ₁, kp₁, e₁⟩ := toCls_isAlpha.1 hα1
  obtain ⟨ρ₂, kp₂, e₂⟩ := toCls_isAlpha.1 hα2
  have hb := cls_beta_of_toClsL hC h3 hβ
  rw [e₁, e₂] at hk
  simp only [toCls, G8Copy.Cls.kap] at hk
  have k1 : kp₁ = 0 := by omega
  have k2 : kp₂ = 0 := by omega
  subst k1 k2
  obtain ⟨g₁, hg₁, hp₁⟩ := gap_pm_atomgapL hC h1 (by rw [e₁]; simp) hx₁ hy₁ hn₁
  obtain ⟨g₂, hg₂, hp₂⟩ := gap_pm_atomgapL hC h2 (by rw [e₂]; simp) hx₂ hy₂ hn₂
  obtain ⟨g₃, hg₃, hp₃⟩ := gap_pm_atomgapL hC h3 (by rw [hb]; simp) hx₃ hy₃ hn₃
  obtain ⟨c₁, hc₁, q₁⟩ := pm_smul_casesL hp₁
  obtain ⟨c₂, hc₂, q₂⟩ := pm_smul_casesL hp₂
  obtain ⟨c₃, hc₃, q₃⟩ := pm_smul_casesL hp₃
  obtain ⟨s₁, s₂, hs₁, hs₂, hs⟩ := hsum
  have hs₁' : (s₁ : ℝ) = 1 ∨ (s₁ : ℝ) = -1 := by rcases hs₁ with h | h <;> simp [h]
  have hs₂' : (s₂ : ℝ) = 1 ∨ (s₂ : ℝ) = -1 := by rcases hs₂ with h | h <;> simp [h]
  rw [← Int.cast_smul_eq_zsmul ℝ s₁, ← Int.cast_smul_eq_zsmul ℝ s₂, q₁, q₂, q₃] at hs
  have hc₃sq : c₃ * c₃ = 1 := by rcases hc₃ with rfl | rfl <;> norm_num
  have hg3 : g₃ = (c₃ * (s₁:ℝ) * c₁) • g₁ + (c₃ * (s₂:ℝ) * c₂) • g₂ := by
    have : c₃ • (c₃ • g₃) = c₃ • ((s₁:ℝ) • c₁ • g₁ + (s₂:ℝ) • c₂ • g₂) := by rw [hs]
    rw [smul_smul, hc₃sq, one_smul, smul_add, smul_smul, smul_smul] at this
    rw [this, smul_smul, smul_smul]
  have hN := hC.N2 hL hη v₁ h1 v₂ h2 v₃ h3 ρ₁ ρ₂ e₁ e₂ hb g₁ g₂ g₃ hg₁ hg₂ hg₃ (c₃ * (s₁:ℝ) * c₁)
    (c₃ * (s₂:ℝ) * c₂) (pm_mul3L hc₃ hs₁' hc₁) (pm_mul3L hc₃ hs₂' hc₂) hg3
  have hlab := dec_labRangeL hC h1 hα1
  have hlab2 := dec_labRangeL hC h2 hα2
  have hLpos : 0 < L := by linarith
  have hnorm : ‖Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x₃ y₃‖ = ‖g₃‖ := norm_gap_of_pm hp₃
  rw [hnorm, e₁, e₂]
  simp only [toCls, G8Copy.Cls.lab]
  have hpos : 0 ≤ L ^ (-50 * η) * min ρ₁ ρ₂ := by
    apply mul_nonneg (Real.rpow_nonneg hLpos.le _)
    rw [e₁] at hlab; rw [e₂] at hlab2
    simp only [toCls, G8Copy.Cls.lab] at hlab hlab2
    exact le_min (le_trans (inv_nonneg.2 hLpos.le) hlab.1) (le_trans (inv_nonneg.2 hLpos.le) hlab2.1)
  linarith

theorem dec_noBetaCutL [Infinite V] {a₀ : V} {v : V} (hv : v ∈ (compMol hf.s.M a₀).atoms)
    (h3 : 3 ≤ (compMol hf.s.M a₀).deg v) {v₂ : V} {x₁ x₂ : PDart hf.s.M (compP hf.s.M a₀)}
    (hcd : (compMol hf.s.M a₀).IsCutData v v₂ x₁ x₂)
    (hg : Molecule.gapAt L (0 : Mom d) (compDecL hf a₀ κ) x₁ x₂ ≠ 0) :
    (compMol hf.s.M a₀).IsAlphaCut v v₂ x₁ x₂ := by
  obtain ⟨v₂', hv₂'⟩ := Infinite.exists_notMem_finset hf.s.M.atoms
  have hvm := (mem_compMol _ _).1 hv
  have hcdM := cutData_ambient hf.s.M a₀ hcd hv₂'
  have h3' : 3 ≤ hf.s.M.deg v := by rwa [compMol_deg _ _ hvm.2] at h3
  exact alphaCut_comp_of_ambient hf.s.M a₀ hcd hv₂' (hC.noBetaCut v hvm.1 h3' v₂' x₁.1 x₂.1 hcdM hg)

end dec4

end WaveTurbulence.FinalCountG3

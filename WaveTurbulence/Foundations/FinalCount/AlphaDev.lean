/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaCount
/-! The `α`-cut (FINALCOUNT-G2 step 4), part 5: the explicit deviation. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem rankFactor_succ (d : ℕ) {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : C₁ ≠ 0) (χ : ℤ) :
    rankFactor d L γ δ C₁ (χ + 1) =
      rankFactor d L γ δ C₁ χ * (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) := by
  unfold rankFactor
  have hb : C₁⁻¹ * δ ^ (1 / 2 : ℝ) ≠ 0 := mul_ne_zero (inv_ne_zero hC) (Real.rpow_pos_of_pos hδ _).ne'
  rw [zpow_add_one₀ hb]
  have : L ^ (-((d : ℝ) - γ) * (((χ + 1 : ℤ)) : ℝ)) = L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * L ^ (-((d : ℝ) - γ)) := by
    rw [← Real.rpow_add hL]; congr 1; push_cast; ring
  rw [this]; ring

/-- **α-cut deviation** (DH23 L1784): `𝔄_pre ≤ N · L^{-(d-γ)} C₁⁻¹ δ^{1/2} (log L)⁴ · 𝔄_pos`, with
`N = (⌊2ρL⌋+1)^d · 2(⌈8δ R L^{2γ}⌉+4)` the number of post classes. -/
theorem alphaCut_isDeviation (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hα : M.IsAlphaCut v v₂ x₁ x₂)
    (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 0 < C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (R ρ : ℝ) (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hgap : ∀ κ, Adm κ → ‖Molecule.gapAt L w κ x₁ x₂‖ ≤ 2 * R)
    (hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ x₁ x₂ - r₀‖ ≤ ρ) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (((alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R ρ : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hE := countE_le_alpha_cut M hcd hdeg L γ δ hδ hL0 w Adm R ρ hR hρ hgap hball
  have hc₀ : 0 ≤ L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (mul_nonneg (inv_nonneg.2 hC.le) (Real.rpow_nonneg hδ.le _))
  have key := countA_cut_dev M hcd hdeg hM L γ δ C₁ w Adm P hL hδ.le hC.le hP0 hPinh
    ((alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R ρ : ℕ) : ℕ∞) _ hc₀ hE (by
      have h := circuitRank_cut_alpha M hcd hα
      have e : M.circuitRank = (M.cut v v₂ x₁ x₂).circuitRank + 1 := by rw [h]; ring
      rw [e, rankFactor_succ d hL0 hδ hC.ne']
      exact le_of_eq (mul_comm _ _))
  rw [ENat.toENNReal_coe] at key
  exact key

end WaveTurbulence.FinalCount

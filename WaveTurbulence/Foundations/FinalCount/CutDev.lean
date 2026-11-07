/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.DevCore
/-! Deviations of a cut (FINALCOUNT-G2 step 3): `𝔄_pre ≤ I · 𝔄_pos` from `𝔈_pre ≤ N · 𝔈_pos`, the circuit-rank
factor and the ladder comparison; the `β`-cut. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The circuit-rank factor of `𝔄`. -/
noncomputable def rankFactor (d : ℕ) (L γ δ C₁ : ℝ) (χ : ℤ) : ℝ :=
  L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χ

theorem rankFactor_nonneg (d : ℕ) {L γ δ C₁ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hC : 0 ≤ C₁) (χ : ℤ) :
    0 ≤ rankFactor d L γ δ C₁ χ := by
  unfold rankFactor
  have : 0 ≤ C₁⁻¹ * δ ^ (1 / 2 : ℝ) := mul_nonneg (inv_nonneg.2 hC) (Real.rpow_nonneg hδ _)
  exact mul_nonneg (Real.rpow_nonneg hL _) (zpow_nonneg this _)

/-- `𝔄` as `𝔈` times the rank factor times the ladder product. -/
theorem countA_eq {d : ℕ} (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P = (M.countE L γ δ w Adm : ℝ≥0∞) *
      ENNReal.ofReal (rankFactor d L γ δ C₁ M.circuitRank *
        ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := by
  unfold Molecule.countA rankFactor; rw [mul_assoc]

/-- **Generic cut deviation.** -/
theorem countA_cut_dev (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 ≤ δ) (hC : 0 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (Nn : ℕ∞) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hE : M.countE L γ δ w Adm ≤ Nn * (M.cut v v₂ x₁ x₂).countE L γ δ w Adm)
    (hrank : rankFactor d L γ δ C₁ M.circuitRank ≤ c₀ * rankFactor d L γ δ C₁ (M.cut v v₂ x₁ x₂).circuitRank) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      ((Nn : ℝ≥0∞) * ENNReal.ofReal (c₀ * Real.log L ^ 4)) := by
  rw [countA_eq, countA_eq]
  have hL0 : 0 ≤ L := (Real.exp_pos 1).le.trans hL
  have hlad := ladderProd_le M hcd hdeg hM (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    (fun S => ladderWeight_ge_one L γ δ (P S) hL hδ (hP0 S)) (fun S => ladderWeight_le L γ δ (P S))
    (fun S' hS' S hS hsub => by simp only [hPinh S' hS' S hS hsub])
  have hΛ : 0 ≤ ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => pow_nonneg (zero_le_one.trans (ladderWeight_ge_one L γ δ (P S) hL hδ (hP0 S))) _
  have hr1 := rankFactor_nonneg d (γ := γ) hL0 hδ hC M.circuitRank
  have hr2 := rankFactor_nonneg d (γ := γ) hL0 hδ hC (M.cut v v₂ x₁ x₂).circuitRank
  refine countA_dev_of_parts _ _ _ _ Nn (c₀ * Real.log L ^ 4) (by positivity) hE ?_
  have hK : (Real.log L ^ 2) ^ 2 = Real.log L ^ 4 := by ring
  rw [hK] at hlad
  calc _ ≤ rankFactor d L γ δ C₁ M.circuitRank * (Real.log L ^ 4 * ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders,
        Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := mul_le_mul_of_nonneg_left hlad hr1
    _ ≤ (c₀ * rankFactor d L γ δ C₁ (M.cut v v₂ x₁ x₂).circuitRank) * (Real.log L ^ 4 * ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders,
        Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :=
        mul_le_mul_of_nonneg_right hrank (mul_nonneg (by positivity) hΛ)
    _ = _ := by ring

/-- **β-cut deviation** (DH23 L1784, first case of Prop 9.4): `𝔄_pre ≤ (4|𝕄|+6)(log L)⁴ 𝔄_pos`. -/
theorem betaCut_isDeviation (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hβ : ¬ M.IsAlphaCut v v₂ x₁ x₂)
    (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 0 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (((4 * M.atoms.card + 6 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.log L ^ 4)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂ := fun h => hβ ((isAlphaCut_iff M hcd).2 h)
  have hE := countE_le_beta_cut M hcd hdeg hsep L γ δ hδ hL0 w Adm
  have key := countA_cut_dev M hcd hdeg hM L γ δ C₁ w Adm P hL hδ.le hC hP0 hPinh
    ((2 * (2 * M.atoms.card + 3) : ℕ) : ℕ∞) 1 zero_le_one hE (by
      rw [circuitRank_cut_beta M hcd hβ]; simp)
  have e : (((2 * (2 * M.atoms.card + 3) : ℕ) : ℕ∞) : ℝ≥0∞) = ((4 * M.atoms.card + 6 : ℕ) : ℝ≥0∞) := by
    rw [ENat.toENNReal_coe]; congr 1; ring
  rw [e, one_mul] at key
  exact key

end WaveTurbulence.FinalCount

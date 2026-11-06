/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceFinalCountInputs
/-! Extract the literal E times ladder-weight product from countA, dividing only by
strictly positive finite source normalization factors. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset
open scoped ENNReal

noncomputable def molecularCountNormalization {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (d : ℕ) (L γ δ C₁ : ℝ) : ℝ :=
  L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank

theorem molecularCountNormalization_pos {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (d : ℕ) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ : ℝ) : 0 < molecularCountNormalization M d L γ δ C₁ := by
  unfold molecularCountNormalization
  exact mul_pos (Real.rpow_pos_of_pos hL _) (zpow_pos (mul_pos (inv_pos.mpr hC₁) (Real.rpow_pos_of_pos hδ _)) _)

theorem countE_mul_ladderWeight_eq_countA_div {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {d : ℕ} (M : Molecule V D) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ : ℝ) (base : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    (M.countE L γ δ base Adm : ℝ≥0∞) * ENNReal.ofReal
      (∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) =
      M.countA L γ δ C₁ base Adm P / ENNReal.ofReal (molecularCountNormalization M d L γ δ C₁) := by
  have ht := molecularCountNormalization_pos M d hL hδ hC₁ γ
  have hzero : ENNReal.ofReal (molecularCountNormalization M d L γ δ C₁) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr ht).ne'
  apply (ENNReal.eq_div_iff hzero ENNReal.ofReal_ne_top).mpr
  unfold Molecule.countA
  change _ = (M.countE L γ δ base Adm : ℝ≥0∞) * ENNReal.ofReal
    (molecularCountNormalization M d L γ δ C₁ * _)
  rw [ENNReal.ofReal_mul ht.le]
  ac_rfl

end WaveTurbulence.LGSpine

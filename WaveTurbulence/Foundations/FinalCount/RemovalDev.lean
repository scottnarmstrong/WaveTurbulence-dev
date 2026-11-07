/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RestrictRank
public import WaveTurbulence.Foundations.FinalCount.AlphaDev
/-! Deviation of removing a union of components (FINALCOUNT-G2 infrastructure for Operations 1 and 2 of DH23
§9.3): `𝔄(𝕄) ≤ N · 𝔄(removed part) · 𝔄(kept part)`-type bound, from a count `𝔈(𝕄) ≤ N 𝔈(kept)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem rankFactor_add (d : ℕ) {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : C₁ ≠ 0) (a b : ℤ) :
    rankFactor d L γ δ C₁ (a + b) = rankFactor d L γ δ C₁ a * rankFactor d L γ δ C₁ b := by
  unfold rankFactor
  have hb : C₁⁻¹ * δ ^ (1 / 2 : ℝ) ≠ 0 := mul_ne_zero (inv_ne_zero hC) (Real.rpow_pos_of_pos hδ _).ne'
  rw [zpow_add₀ hb]
  have : L ^ (-((d : ℝ) - γ) * (((a + b : ℤ)) : ℝ)) =
      L ^ (-((d : ℝ) - γ) * (a : ℝ)) * L ^ (-((d : ℝ) - γ) * (b : ℝ)) := by
    rw [← Real.rpow_add hL]; congr 1; push_cast; ring
  rw [this]; ring

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)

/-- **Removal deviation.** If `𝔈(𝕄) ≤ N · 𝔈(kept)` then `𝔄(𝕄) ≤ N · 𝔞(removed) · 𝔄(kept)`, where
`𝔞(removed) = L^{-(d-γ)χ'} (C₁⁻¹δ^{1/2})^{χ'} ∏ 𝔛^z` over the removed part. -/
theorem removal_isDeviation (L γ δ C₁ : ℝ) (w : Mom d) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : ((PDart M P) → (Fin d → ℤ)) → Prop)
    (Pl : Finset V → ℝ) (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (Pl S))
    (Nn : ℕ∞) (hE : M.countE L γ δ w Adm ≤ Nn * (restrictP M P h).countE L γ δ w Adm') :
    IsDeviation (M.countA L γ δ C₁ w Adm Pl) ((restrictP M P h).countA L γ δ C₁ w Adm' Pl)
      ((Nn : ℝ≥0∞) * ENNReal.ofReal (rankFactor d L γ δ C₁ (restrictP M (fun a => ¬ P a) h.neg).circuitRank *
        ∏ S ∈ (restrictP M (fun a => ¬ P a) h.neg).maximalLadders,
          Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S)) := by
  rw [countA_eq, countA_eq]
  have hrk := circuitRank_restrictP_add M P h
  have hrf : rankFactor d L γ δ C₁ M.circuitRank =
      rankFactor d L γ δ C₁ (restrictP M P h).circuitRank *
        rankFactor d L γ δ C₁ (restrictP M (fun a => ¬ P a) h.neg).circuitRank := by
    rw [← rankFactor_add d hL hδ hC.ne', hrk]
  have hlad := ladderProd_restrictP M P h (fun S => Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S)
  have hnn : 0 ≤ rankFactor d L γ δ C₁ (restrictP M (fun a => ¬ P a) h.neg).circuitRank *
        ∏ S ∈ (restrictP M (fun a => ¬ P a) h.neg).maximalLadders,
          Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S :=
    mul_nonneg (rankFactor_nonneg d hL.le hδ.le hC.le _)
      (Finset.prod_nonneg fun S _ => pow_nonneg (hX S) _)
  refine countA_dev_of_parts _ _ _ _ Nn _ hnn hE (le_of_eq ?_)
  rw [hrf, hlad]; ring

end WaveTurbulence.FinalCount

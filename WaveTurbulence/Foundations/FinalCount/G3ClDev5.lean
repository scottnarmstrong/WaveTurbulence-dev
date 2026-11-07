/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev4
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev5
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the deviation of a cluster erasure** (set version of `erase0_isDeviation`).

With `𝔈(M) ≤ N 𝔈(M - K)` (`G3ClDev3/4`), the rank drop `j` (`χ(M) = χ(M - K) + j`, `G3ClDev2.circuitRank_eraseSet`) and the ladder ratio `Λ`:
`𝔄(M) ≤ N · rankFactor(j) · Λ · 𝔄(M - K)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {K : Finset V}

/-- **The deviation of a cluster erasure of `𝔄`.** -/
theorem eraseSet_isDeviation {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁) {w : Mom d}
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)) (Nn : ℕ∞) (Λ : ℝ) (hΛ : 0 ≤ Λ) (j : ℤ)
    (hrk : M.circuitRank = (eraseSet M K).circuitRank + j)
    (hE : M.countE L γ δ w Adm ≤ Nn * (eraseSet M K).countE L γ δ w Adm')
    (hlad : ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
      Λ * ∏ S ∈ (eraseSet M K).maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((eraseSet M K).countA L γ δ C₁ w Adm' P)
      ((Nn : ℝ≥0∞) * ENNReal.ofReal (rankFactor d L γ δ C₁ j * Λ)) := by
  rw [countA_eq, countA_eq]
  have hrf : rankFactor d L γ δ C₁ M.circuitRank = rankFactor d L γ δ C₁ (eraseSet M K).circuitRank *
      rankFactor d L γ δ C₁ j := by
    rw [← rankFactor_add d hL hδ hC.ne', hrk]
  have hnn : 0 ≤ rankFactor d L γ δ C₁ j * Λ :=
    mul_nonneg (rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le _) hΛ
  refine countA_dev_of_parts _ _ _ _ Nn _ hnn hE ?_
  rw [hrf]
  have hrn := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le (eraseSet M K).circuitRank
  have hrn2 := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le j
  calc _ ≤ rankFactor d L γ δ C₁ (eraseSet M K).circuitRank * rankFactor d L γ δ C₁ j *
          (Λ * ∏ S ∈ (eraseSet M K).maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.FinalCountG3

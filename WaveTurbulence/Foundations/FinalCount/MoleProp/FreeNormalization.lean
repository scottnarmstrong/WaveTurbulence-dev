/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.Degen.NormalizationFactors
public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitNormalization
import Mathlib.Tactic

/-! # Exact normalization for the unrestricted-charge per-position count -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def freeNormalization (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ)
    (P : Finset V → ℝ) : ℝ :=
  L ^ (-((d : ℝ)-γ)*M.circuitRank) * (C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank * cellProduct M L γ δ P

theorem countAFree_eq_normalization (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P =
      (countEFree M L γ δ w Adm : ℝ≥0∞)*ENNReal.ofReal (freeNormalization M (d := d) L γ δ C1 P) := rfl

theorem cellProduct_pos (M : Molecule V D) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlog : 0 < Real.log L ^ 2) (P : Finset V → ℝ) (hP : ∀ S ∈ ladderCells M, 0 ≤ P S) :
    0 < cellProduct M L γ δ P := by
  unfold cellProduct
  apply prod_pos
  intro S hS
  unfold Molecule.ladderWeight
  apply lt_min hlog
  have ht := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2*γ))) (hP S hS)
  linarith only [ht]

theorem freeNormalization_pos (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (hlog : 0 < Real.log L ^ 2)
    (P : Finset V → ℝ) (hP : ∀ S ∈ ladderCells M, 0 ≤ P S) :
    0 < freeNormalization M (d := d) L γ δ C1 P := by
  unfold freeNormalization
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hL _)
    (zpow_pos (by positivity : 0 < C1⁻¹*δ^(1/2 : ℝ)) _)) (cellProduct_pos M hL.le hδ.le hlog P hP)

/-- A conditional scalar assembly helper, not a source counting theorem. -/
theorem countAFree_le_ratio_of_countEFree_le {D' : Type*} [Fintype D'] [DecidableEq D']
    (M : Molecule V D) (M' : Molecule V D') {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (D' → (Fin d → ℤ)) → Prop)
    (P P' : Finset V → ℝ) (K : ℕ)
    (hc : countEFree M L γ δ w Adm ≤ (K : ℕ∞)*countEFree M' L γ δ w Adm')
    (hpre : 0 ≤ freeNormalization M (d := d) L γ δ C1 P)
    (hpost : 0 < freeNormalization M' (d := d) L γ δ C1 P') :
    countAFree M L γ δ C1 w Adm P ≤
      ENNReal.ofReal ((K : ℝ)*freeNormalization M (d := d) L γ δ C1 P /
        freeNormalization M' (d := d) L γ δ C1 P') * countAFree M' L γ δ C1 w Adm' P' := by
  rw [countAFree_eq_normalization,countAFree_eq_normalization]
  exact Degen.normalized_count_mono hc hpre hpost

end WaveTurbulence.MoleProp

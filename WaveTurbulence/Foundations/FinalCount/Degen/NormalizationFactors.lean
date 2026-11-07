/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CountEDeletion
public import WaveTurbulence.Foundations.FinalCount.Degen.CountEFixedLabel
import Mathlib.Tactic

/-! # Exact scalar normalization of the source countE inequalities

All actual maximal-ladder factors are retained in this module. Their
geometric comparison is a separate proof, not a hypothesis concealed here.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The literal maximal-ladder product in TARGET defcounta2. -/
noncomputable def ladderProduct (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) : ℝ :=
  ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S

/-- The literal scalar multiplying countE in the exact B2 countA definition. -/
noncomputable def normalizationFactor (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ)
    (P : Finset V → ℝ) : ℝ :=
  L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
    ladderProduct M L γ δ P

theorem ladderProduct_pos (M : Molecule V D) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlog : 0 < Real.log L ^ 2) (P : Finset V → ℝ) (hP : ∀ S ∈ M.maximalLadders, 0 ≤ P S) :
    0 < ladderProduct M L γ δ P := by
  unfold ladderProduct
  apply prod_pos
  intro S hS
  apply pow_pos
  unfold Molecule.ladderWeight
  apply lt_min hlog
  have hterm : 0 ≤ δ * L ^ (2 * γ) * P S :=
    mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL _)) (hP S hS)
  linarith only [hterm]

theorem normalizationFactor_pos (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (hlog : 0 < Real.log L ^ 2)
    (P : Finset V → ℝ) (hP : ∀ S ∈ M.maximalLadders, 0 ≤ P S) :
    0 < normalizationFactor M (d := d) L γ δ C1 P := by
  unfold normalizationFactor
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hL _)
    (zpow_pos (by positivity : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ)) _)) (ladderProduct_pos M hL.le hδ.le hlog P hP)

/-- Explicit equality with the source countA; no alternate normalized count. -/
theorem countA_eq_normalization (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ C1 w Adm P =
      (M.countE L γ δ w Adm : ℝ≥0∞) * ENNReal.ofReal (normalizationFactor M (d := d) L γ δ C1 P) := rfl

/-- Multiplying the count inequality by the exact normalization gives the
exact normalized ratio, including all actual ladder factors. -/
theorem normalized_count_mono {A B : ℕ∞} {K : ℕ} {a b : ℝ}
    (hcount : A ≤ K * B) (ha : 0 ≤ a) (hb : 0 < b) :
    (A : ℝ≥0∞) * ENNReal.ofReal a ≤
      ENNReal.ofReal ((K : ℝ) * a / b) * ((B : ℝ≥0∞) * ENNReal.ofReal b) := by
  have hh := ENat.toENNReal_mono hcount
  rw [ENat.toENNReal_mul] at hh
  calc
    _ ≤ ((K : ℝ≥0∞) * (B : ℝ≥0∞)) * ENNReal.ofReal a := mul_le_mul_of_nonneg_right hh bot_le
    _ = ENNReal.ofReal ((K : ℝ) * a / b) * ((B : ℝ≥0∞) * ENNReal.ofReal b) := by
      have hscalar : ENNReal.ofReal ((K : ℝ) * a / b) * ENNReal.ofReal b =
          ENNReal.ofReal (K : ℝ) * ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ) * a / b)]
        rw [show (K : ℝ) * a / b * b = (K : ℝ) * a by field_simp]
        exact ENNReal.ofReal_mul (Nat.cast_nonneg K)
      rw [show (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) by simp only [ENNReal.ofReal_natCast]]
      calc
        _ = (ENNReal.ofReal (K : ℝ) * ENNReal.ofReal a) * (B : ℝ≥0∞) := by ring
        _ = (ENNReal.ofReal ((K : ℝ) * a / b) * ENNReal.ofReal b) * (B : ℝ≥0∞) := by rw [hscalar]
        _ = _ := by ring

end WaveTurbulence.Degen

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmClass2
/-! **FINALCOUNT-ASSEMBLY (garden wrapper): the constant `C₁ → C₁/4`.**  `countA` at `C₁/4` is `4^χ` times `countA` at `C₁`
(`χ` the circuit rank), so a class bound at `C₁/4` gives the factor `4^{-χ}` that absorbs `2^n`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem countA_quarter (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ (C₁ / 4) w Adm P = ENNReal.ofReal (4 ^ M.circuitRank) * M.countA L γ δ C₁ w Adm P := by
  unfold Molecule.countA
  have h4 : (C₁ / 4)⁻¹ = 4 * C₁⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have e : L ^ (-((d : ℝ) - γ) * M.circuitRank) * ((C₁ / 4)⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
        ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S =
      4 ^ M.circuitRank * (L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
        ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := by
    rw [h4, mul_assoc 4 C₁⁻¹ (δ ^ (1 / 2 : ℝ)), mul_zpow (4 : ℝ) (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) M.circuitRank]; ring
  rw [e, ENNReal.ofReal_mul (by positivity)]
  ring

/-- The class factor: `2^n (2R+1)^{2R} 4^{-(n-R+1)} ≤ (36 R²)^R` for `R ≥ 1`. -/
theorem class_factor_le (n R : ℕ) (hR : 1 ≤ R) :
    (2 : ℝ) ^ n * (2 * (R : ℝ) + 1) ^ (2 * R) * (4 : ℝ) ^ (-((n : ℤ) - R + 1)) ≤ (36 * (R : ℝ) ^ 2) ^ R := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have h1 : (2 : ℝ) ^ n * (4 : ℝ) ^ (-((n : ℤ) - R + 1)) ≤ 4 ^ R := by
    have e : (4 : ℝ) ^ (-((n : ℤ) - R + 1)) = (4 : ℝ) ^ R / 4 / 4 ^ n := by
      rw [show -((n : ℤ) - R + 1) = (R : ℤ) + (-1) + (-(n : ℤ)) by ring, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_assoc]
    rw [e]
    have h4n : (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h4n0 : (0 : ℝ) < 4 ^ n := by positivity
    calc (2 : ℝ) ^ n * ((4 : ℝ) ^ R / 4 / 4 ^ n) = (2 ^ n / 4 ^ n) * ((4 : ℝ) ^ R / 4) := by ring
      _ ≤ 1 * ((4 : ℝ) ^ R / 4) := by
          gcongr
          rw [div_le_one h4n0]; exact h4n
      _ ≤ 4 ^ R := by nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) R]
  have h2 : (2 * (R : ℝ) + 1) ^ (2 * R) ≤ (9 * (R : ℝ) ^ 2) ^ R := by
    have hsq : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * (R : ℝ) ^ 2 := by nlinarith
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hsq R
  have h3 : (36 * (R : ℝ) ^ 2) ^ R = 4 ^ R * (9 * (R : ℝ) ^ 2) ^ R := by rw [← mul_pow]; ring_nf
  rw [h3]
  calc (2 : ℝ) ^ n * (2 * (R : ℝ) + 1) ^ (2 * R) * (4 : ℝ) ^ (-((n : ℤ) - R + 1))
      = ((2 : ℝ) ^ n * (4 : ℝ) ^ (-((n : ℤ) - R + 1))) * (2 * (R : ℝ) + 1) ^ (2 * R) := by ring
    _ ≤ 4 ^ R * (9 * (R : ℝ) ^ 2) ^ R := mul_le_mul h1 h2 (by positivity) (by positivity)

theorem countA_of_quarter (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P = ENNReal.ofReal (4 ^ (-M.circuitRank)) * M.countA L γ δ (C₁ / 4) w Adm P := by
  rw [countA_quarter, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : (4 : ℝ) ^ (-M.circuitRank) * 4 ^ M.circuitRank = 1 := by
    rw [← zpow_add₀ (by norm_num)]; simp
  rw [this]; simp

/-- **The class sum.**  If every class (over the finite label set `S`) has `countA` at `C₁/4` at most `B`, then `countA` at `C₁`
is at most `|S| · 4^{-χ} · B`. -/
theorem countA_le_sum_classes {ι : Type*} (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (S : Finset ι)
    {Adm : (D → (Fin d → ℤ)) → Prop} (Adm' : ι → (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (h : ∀ κ, Adm κ → ∃ j ∈ S, Adm' j κ) {B : ℝ} (hB : 0 ≤ B)
    (hcl : ∀ j ∈ S, M.countA L γ δ (C₁ / 4) w (Adm' j) P ≤ ENNReal.ofReal B) :
    M.countA L γ δ C₁ w Adm P ≤ ENNReal.ofReal ((S.card : ℝ) * 4 ^ (-M.circuitRank) * B) := by
  refine (countA_union_le M L γ δ C₁ w S Adm' h P).trans ?_
  calc ∑ j ∈ S, M.countA L γ δ C₁ w (Adm' j) P
      = ∑ j ∈ S, ENNReal.ofReal (4 ^ (-M.circuitRank)) * M.countA L γ δ (C₁ / 4) w (Adm' j) P :=
        Finset.sum_congr rfl fun j _ => countA_of_quarter M L γ δ C₁ w _ P
    _ ≤ ∑ j ∈ S, ENNReal.ofReal (4 ^ (-M.circuitRank)) * ENNReal.ofReal B :=
        Finset.sum_le_sum fun j hj => mul_le_mul' le_rfl (hcl j hj)
    _ = ENNReal.ofReal ((S.card : ℝ) * 4 ^ (-M.circuitRank) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), mul_assoc]

end WaveTurbulence.FinalCountAsm

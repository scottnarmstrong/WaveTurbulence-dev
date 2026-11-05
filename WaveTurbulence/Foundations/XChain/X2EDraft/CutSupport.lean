/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.TIDecay
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DyadicReduction

/-!
# X2E-5, step 2: the cutoff supports and the coefficient gains

**Statements** (flower coefficients `fkCoef`, `|coupling| ≤ 1`):
- `dyadicCut_eq_zero_of_le`: for `j ≥ 1`, `dyadicCut L j x = 0` when `0 ≤ x ≤ 2^j L/4`;
- `norm_fkCoef_plain_cut2_le` (`M₂`): plain pattern, `cut2 = j₂ ≥ 1`, `p < s < t ≤ p + 1`:
  `‖fkCoef‖ ≤ 8/(πδL^{2γ} 2^{j₂}L)`. A stem node `≠ 𝔣^pr` has `|Ω| > 2^{j₂}L/4`, and `norm_TIpat_plain_le` applies;
- `exists_big_leaf_of_fkCoef_ne` (`M₁`): `cut1 = j₁ ≥ 1`, `fkCoef ≠ 0` ⟹ a non-flower leaf has `|k| > 2^{j₁}L/4`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Set Induct SysAPI Cpl
open scoped Classical

theorem dyadicCut_eq_zero_of_le {L : ℝ} (hL : 0 < L) {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 ^ j * L / 4) : dyadicCut L j x = 0 := by
  unfold dyadicCut
  rw [ite_eq_right (by omega : j ≠ 0)]
  have h2 : (0 : ℝ) < 2 ^ j * L := by positivity
  have h3 : (0 : ℝ) < 2 ^ (j - 1) * L := by positivity
  have e : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have ha : chi0 (x / (2 ^ j * L)) = 1 := by
    refine Fixedpt.chi0_eq_one ?_
    rw [abs_of_nonneg (by positivity), div_le_iff₀ h2]
    linarith
  have hb : chi0 (x / (2 ^ (j - 1) * L)) = 1 := by
    refine Fixedpt.chi0_eq_one ?_
    rw [abs_of_nonneg (by positivity), div_le_iff₀ h3]
    rw [e] at hx
    linarith
  rw [ha, hb, sub_self]

section Coef

variable (L γ δ : ℝ) {d : ℕ} (p : ℕ) (dagger : Option (Fin 3 → Mom d)) (t s : ℝ)

/-- **The `M₂` gain of a plain flower coefficient.** -/
theorem norm_fkCoef_plain_cut2_le (cut1 : Option ℕ) (hc : |coupling d L γ δ| ≤ 1) (hδ : 0 < δ) (hL : 0 < L)
    {j₂ : ℕ} (hj : 1 ≤ j₂) (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1) (F : FTree)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ‖fkCoef L γ δ p .plain dagger cut1 (some j₂) t s F κ‖ ≤
      8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) := by
  have hLγ : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  have hpos : 0 < Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L) := by positivity
  unfold fkCoef
  by_cases hF : F = FTree.flower
  · rw [dite_eq_left hF, norm_zero]
    positivity
  rw [dite_eq_right hF, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_treePrefactor_le_one L γ δ F.toTree hc
  have h2 := norm_epsProd_le F.toTree κ
  set x : ℝ := (((univ.filter fun b : GBranch (single F.toTree) => OnStemT F b ∧ b ≠ F.flowerParent hF).sup
    fun b => ‖omegaT L F.toTree κ b‖₊ : NNReal) : ℝ) with hxdef
  by_cases hx : x ≤ 2 ^ j₂ * L / 4
  · have h0 : treeCut2 L F hF j₂ κ = 0 := dyadicCut_eq_zero_of_le hL hj (NNReal.coe_nonneg _) hx
    have hw : treeWeight L F hF dagger cut1 (some j₂) κ = 0 := by
      unfold treeWeight
      change _ * treeCut2 L F hF j₂ κ * _ = 0
      rw [h0, mul_zero, zero_mul]
    rw [hw, abs_zero, mul_zero, zero_mul, mul_zero]
    positivity
  · push Not at hx
    have hne : (univ.filter fun b : GBranch (single F.toTree) => OnStemT F b ∧ b ≠ F.flowerParent hF).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hxdef, hne, sup_empty] at hx
      have : (0 : ℝ) < 2 ^ j₂ * L / 4 := by positivity
      simp only [bot_eq_zero', NNReal.coe_zero] at hx
      linarith
    obtain ⟨c, hcmem, hcsup⟩ := Finset.exists_mem_eq_sup _ hne fun b => ‖omegaT L F.toTree κ b‖₊
    obtain ⟨-, hcne⟩ := (mem_filter.mp hcmem).2
    have hΩ : 2 ^ j₂ * L / 4 < |omegaT L F.toTree κ c| := by
      rw [hxdef, hcsup, coe_nnnorm, Real.norm_eq_abs] at hx
      exact hx
    have hoff : c ∉ (if dagger.isSome then {F.flowerParent hF} else ∅ : Finset (GBranch (single F.toTree))) := by
      split_ifs
      · exact fun h => hcne (mem_singleton.mp h)
      · exact notMem_empty _
    have hΩ0 : omegaT L F.toTree κ c ≠ 0 := fun h => by
      rw [h, abs_zero] at hΩ
      have : (0 : ℝ) < 2 ^ j₂ * L / 4 := by positivity
      linarith
    have h4 := norm_TIpat_plain_le L γ δ hF p _ κ hps hst ht c hcne hoff hδ hL hΩ0
    have h3 := Fixedpt.abs_treeWeight_le_one L hF dagger cut1 (some j₂) κ
    have h5 : 2 / (Real.pi * δ * L ^ (2 * γ) * |omegaT L F.toTree κ c|) ≤
        8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)) := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      have hpd : 0 < Real.pi * δ * L ^ (2 * γ) := by positivity
      nlinarith
    calc _ ≤ 1 * (1 * 1 * (8 / (Real.pi * δ * L ^ (2 * γ) * (2 ^ j₂ * L)))) :=
          mul_le_mul h1 (mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) (h4.trans h5)
            (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
      _ = _ := by ring

/-- **The `M₁` support of a flower coefficient.** -/
theorem exists_big_leaf_of_fkCoef_ne (pat : FixPat) (cut2 : Option ℕ) (hL : 0 < L) {j₁ : ℕ} (hj : 1 ≤ j₁)
    (F : FTree) (κ : GNode (single F.toTree) → (Fin d → ℤ))
    (h : fkCoef L γ δ p pat dagger (some j₁) cut2 t s F κ ≠ 0) :
    ∃ ℓ ∈ univ.erase F.flowerLeaf, 2 ^ j₁ * L / 4 < ‖latticePoint L (κ ℓ.toNode)‖ := by
  by_contra hno
  push Not at hno
  apply h
  unfold fkCoef
  by_cases hF : F = FTree.flower
  · exact dite_eq_left hF
  rw [dite_eq_right hF]
  have hx : (((univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ ℓ.toNode)‖₊ : NNReal) : ℝ) ≤
      2 ^ j₁ * L / 4 := by
    have hr : (0 : ℝ) ≤ 2 ^ j₁ * L / 4 := by positivity
    have : ((univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ ℓ.toNode)‖₊) ≤
        Real.toNNReal (2 ^ j₁ * L / 4) := Finset.sup_le fun ℓ hℓ =>
      (Real.le_toNNReal_iff_coe_le hr).mpr (by rw [coe_nnnorm]; exact hno ℓ hℓ)
    have h' := NNReal.coe_le_coe.mpr this
    rwa [Real.coe_toNNReal _ hr] at h'
  have h0 : treeCut1 L F j₁ κ = 0 := dyadicCut_eq_zero_of_le hL hj (NNReal.coe_nonneg _) hx
  have hw : treeWeight L F hF dagger (some j₁) cut2 κ = 0 := by
    unfold treeWeight
    change treeCut1 L F j₁ κ * _ * _ = 0
    rw [h0, zero_mul, zero_mul]
  rw [hw, Complex.ofReal_zero, mul_zero, zero_mul, mul_zero]

end Coef

end WaveTurbulence.X2E

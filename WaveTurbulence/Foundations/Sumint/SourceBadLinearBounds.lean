/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceLinearBranch
public import WaveTurbulence.Foundations.Sumint.StrictPowerAbsorption

/-!
# The actual case-(b) gain and case-(d) linear cost

The case-(b) external momentum norm cancels the reciprocal norm in the
first linear estimate. In case (d) the better branch costs gammaBase;
a further half of gammaBase absorbs its fixed delta coefficient. Both
thresholds are uniform in the datum and block count.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint case (b): the external norm and actual linear mass have a strict bad gain. -/
theorem exists_source_case_b_linear_bound (d : ℕ) {γ : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (η : ℝ), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      r ≠ 0 → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c h : ℝ) (i : Fin D.S.I), h ∈ Icc (0:ℝ) 1 →
      ENNReal.ofReal ‖r‖*linearFactorMass D L γ δ p ν r t c h i ≤
      ENNReal.ofReal (L^((d:ℝ)-γ-gammaBase γ/2)) := by
  have hb : gammaBase γ ≤ γ := min_le_left _ _
  have hgap : (d:ℝ)-2*γ < (d:ℝ)-γ-gammaBase γ/2 := by linarith [hγ.1]
  obtain ⟨R,hR,hbound⟩ := exists_coefficient_power_le (δ⁻¹*scaledLinearConstant d)
    ((d:ℝ)-2*γ) ((d:ℝ)-γ-gammaBase γ/2) hgap
  refine ⟨R,hR,?_⟩
  intro L hL D η hγη p ν r hr hrupper t c h i hh
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hab := enlargedTimeLower_le_upper D c hh.1 (.inl ⟨i,0⟩)
  have hlen : enlargedTimeUpper D c h (.inl ⟨i,0⟩)-enlargedTimeLower D c h (.inl ⟨i,0⟩) ≤ 3 := by
    dsimp [enlargedTimeUpper,enlargedTimeLower]
    linarith [hh.2]
  rw [linearFactorMass_eq_ofReal_integral D hLp,← ENNReal.ofReal_mul (norm_nonneg r)]
  apply ENNReal.ofReal_le_ofReal
  exact (norm_mul_integral_linearTimeSum_le D hL1 hδ γ p ν r hr t i hab
    (source_linear_short_window hL1 hδ.le hδsmall hγη hab hlen r hrupper)).trans (hbound L hL)

/-- TARGET sumint case (d): the actual linear mass costs at most three halves of gammaBase. -/
theorem exists_source_case_d_linear_bound (d : ℕ) {γ : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (η : ℝ), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c h : ℝ) (i : Fin D.S.I), h ∈ Icc (0:ℝ) 1 →
      linearFactorMass D L γ δ p ν r t c h i ≤
      ENNReal.ofReal (L^((d:ℝ)-γ+3*gammaBase γ/2)) := by
  have hb := gammaBase_pos hγ
  obtain ⟨R,hR,hbound⟩ := exists_coefficient_power_le (sourceLinearBranchConstant d*δ⁻¹)
    ((d:ℝ)-γ+gammaBase γ) ((d:ℝ)-γ+3*gammaBase γ/2) (by linarith only [hb])
  refine ⟨R,hR,?_⟩
  intro L hL D η hγη p ν r hr hrupper t c h i hh
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  exact (linearFactorMass_le_best_branch D hL1 hδ hδsmall hγη p ν r hr hrupper t c hh i).trans
    (ENNReal.ofReal_le_ofReal (hbound L hL))

end WaveTurbulence.Sumint

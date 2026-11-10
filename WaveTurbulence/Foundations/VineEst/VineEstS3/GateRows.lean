/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ThetaMono
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Lead
public import WaveTurbulence.Foundations.Spine.RestrictionNormCalculus

/-! # Row bounds of `K*_Q`, `K*_T` from the Prop 6.1 (30d) and Prop 5.1 gates (Step 3, gate matching)

`couple_row_le`, `tree_row_le`: for an eligible regular object of order `n` and incoherency index `g`, the restriction
norm `𝔛^{6η⁶,30d,·}(box)` of its starred kernel is at most `rowB P n g = cb C₁² (2C₁²δ)ⁿ L^{-(γ₁-√η)g}`.
For `g ≥ 1` this is B2.2 (`IncoherentGateAt`); for `g = 0` it is the 30d Prop 6.1 gate plus the separated bound.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.PL2330 WaveTurbulence.LGSpine WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

/-- The row constant `1 + (2d)^{30d}`. -/
noncomputable def rowCb (P : WTParams) : ℝ := 1 + cLeib P.d (30 * P.d)

/-- The row bound `cb C₁² (2C₁²δ)ⁿ L^{-(γ₁-√η) g}`. -/
noncomputable def rowB (P : WTParams) (n g : ℕ) : ℝ :=
  rowCb P * P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))

theorem rowB_pos {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (n g : ℕ) : 0 < rowB P n g := by
  have : 0 < rowCb P := by unfold rowCb; have := cLeib_nonneg P.d (30 * P.d); linarith
  unfold rowB
  have : 0 < P.C₁ := by linarith
  positivity

theorem regBound_le_rowB {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    regBound P n g ≤ ENNReal.ofReal (rowB P n g) := by
  unfold regBound
  apply ENNReal.ofReal_le_ofReal
  unfold rowB rowCb
  have hc : 0 < P.C₁ := by linarith
  have hLb := cLeib_nonneg P.d (30 * P.d)
  have h1 : (P.C₁ * P.δ) ^ n ≤ (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (P.C₁ - 1)]
  have h2 : P.C₁ ≤ (1 + cLeib P.d (30 * P.d)) * P.C₁ ^ 2 := by nlinarith
  have h3 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg hL _
  calc P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
      ≤ ((1 + cLeib P.d (30 * P.d)) * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- The coherent total: `regBound P n 1 + (separated bound) ≤ rowB P n 0`. -/
theorem coherent_total_le {P : WTParams} (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (n : ℕ) :
    regBound P n 1 + ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) *
      (P.C₁ * P.C₁ ^ n))) ≤ ENNReal.ofReal (rowB P n 0) := by
  have hc : 0 < P.C₁ := by linarith
  have hLb := cLeib_nonneg P.d (30 * P.d)
  have hL0 : 0 ≤ P.L := by linarith
  have hreg : regBound P n 1 ≤ ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n) := by
    unfold regBound
    apply ENNReal.ofReal_le_ofReal
    have : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hL
      push_cast; nlinarith
    calc P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))
        ≤ P.C₁ * (P.C₁ * P.δ) ^ n * 1 := by gcongr
      _ = _ := mul_one _
  refine (add_le_add_left hreg _).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold rowB rowCb
  have h1 : (P.C₁ * P.δ) ^ n ≤ (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (P.C₁ - 1)]
  have h0 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((0 : ℕ) : ℝ)) = 1 := by simp
  rw [h0]
  have e2 : (2 : ℝ) ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * (P.C₁ * P.C₁ ^ n)) * (P.C₁ * P.C₁ ^ n)) =
      cLeib P.d (30 * P.d) * (P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n) := by
    rw [mul_pow, mul_pow]; ring
  rw [e2]
  have : P.C₁ * (P.C₁ * P.δ) ^ n ≤ P.C₁ ^ 2 * (2 * P.C₁ ^ 2 * P.δ) ^ n := by
    calc P.C₁ * (P.C₁ * P.δ) ^ n ≤ P.C₁ ^ 2 * (P.C₁ * P.δ) ^ n := by gcongr; nlinarith
      _ ≤ _ := by gcongr
  nlinarith

end WaveTurbulence.VineEstS3

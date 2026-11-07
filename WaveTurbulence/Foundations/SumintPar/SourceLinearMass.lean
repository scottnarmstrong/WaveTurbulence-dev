/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceTimeContinuity
public import WaveTurbulence.Foundations.SumintPar.SourceNormalizedLinear
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry

/-!
# The distinguished source mass on its literal enlarged interval

The nonnegative mass equals the ofReal of the ordinary integral.
The short-window condition is derived from the source output momentum
bound, so the F23 estimate requires no additional window hypothesis.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- Distinguished linear mass on the actual source interval. -/
@[expose] noncomputable def linearFactorMass {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : Fin D.S.I) : ℝ≥0∞ :=
  ∫⁻ s in Icc (enlargedTimeLower D c h (.inl ⟨i,0⟩))
    (enlargedTimeUpper D c h (.inl ⟨i,0⟩)), ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i s‖

/-- The actual distinguished mass is the ordinary compact-interval norm integral. -/
theorem linearFactorMass_eq_ofReal_integral {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : Fin D.S.I) :
    linearFactorMass D L γ δ p ν r t c h i =
      ENNReal.ofReal (∫ s in Icc (enlargedTimeLower D c h (.inl ⟨i,0⟩))
        (enlargedTimeUpper D c h (.inl ⟨i,0⟩)), ‖linearTimeSum D L γ δ p ν r t i s‖) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    ((continuous_linearTimeSum D hL γ δ p ν r t i).norm.continuousOn.integrableOn_compact isCompact_Icc)
    (ae_of_all _ (fun _ => norm_nonneg _))

/-- The actual linear mass has the uniform trivial bound on every enlarged unit interval. -/
theorem linearFactorMass_le_trivial {d : ℕ} (D : SumintDatum d) {L δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
    {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) (i : Fin D.S.I) :
    linearFactorMass D L γ δ p ν r t c h i ≤ ENNReal.ofReal (3*(12:ℝ)^d*L^(d:ℝ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hc : 0 < sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  have hab := enlargedTimeLower_le_upper D c hh.1 (.inl ⟨i,0⟩)
  have hlen : enlargedTimeUpper D c h (.inl ⟨i,0⟩)-enlargedTimeLower D c h (.inl ⟨i,0⟩) ≤ 3 := by
    dsimp [enlargedTimeUpper,enlargedTimeLower]
    linarith [hh.2]
  rw [linearFactorMass_eq_ofReal_integral D hLp]
  apply ENNReal.ofReal_le_ofReal
  apply (integral_linearTimeSum_le_trivial D (by linarith : 1 ≤ 4*L) γ δ hc p ν r t i hab).trans
  calc
    _ ≤ 3*(3:ℝ)^d*(4*L)^d := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlen (by positivity)) (by positivity)
    _ = _ := by rw [mul_pow,Real.rpow_natCast,show (12:ℝ) = 3*4 by norm_num,mul_pow]; ring

/-- F23 on the actual source interval, with its short-window condition discharged. -/
theorem linearFactorMass_le_f23 {d : ℕ} (D : SumintDatum d) {L γ η δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) (hγη : γ+η ≤ 1)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (hr : 1/L ≤ ‖r‖) (hrupper : ‖r‖ ≤ L^(-γ+η)) (t c : ℝ) {h : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) (i : Fin D.S.I) :
    linearFactorMass D L γ δ p ν r t c h i ≤
      ENNReal.ofReal (δ⁻¹*scaledLinearConstant d*L^((d:ℝ)+1-2*γ)) := by
  have hab := enlargedTimeLower_le_upper D c hh.1 (.inl ⟨i,0⟩)
  have hlen : enlargedTimeUpper D c h (.inl ⟨i,0⟩)-enlargedTimeLower D c h (.inl ⟨i,0⟩) ≤ 3 := by
    dsimp [enlargedTimeUpper,enlargedTimeLower]
    linarith [hh.2]
  rw [linearFactorMass_eq_ofReal_integral D (zero_lt_one.trans_le hL)]
  exact ENNReal.ofReal_le_ofReal (integral_linearTimeSum_le_f23 D hL hδ γ p ν r hr t i hab
    (source_linear_short_window hL hδ.le hδsmall hγη hab hlen r hrupper))

end WaveTurbulence.SumintPar

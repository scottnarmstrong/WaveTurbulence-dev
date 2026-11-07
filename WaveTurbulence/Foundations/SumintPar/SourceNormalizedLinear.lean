/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLinearWindow
public import WaveTurbulence.Foundations.SumintPar.SourceScalePowers

/-!
# Normalized source linear estimates, including F23

The exact width-four rescaling fixes the dimension constant. The basic
cancellation branch cancels the external norm in case (b); the lattice
lower bound on that norm gives the second branch needed for case (d).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- The explicit dimension constant after the source width-four rescaling. -/
@[expose] noncomputable def scaledLinearConstant (d : ℕ) : ℝ :=
  (4:ℝ)^d/2*LemLin.linearCancellationConstant d

theorem scaledLinearConstant_nonneg (d : ℕ) : 0 ≤ scaledLinearConstant d :=
  mul_nonneg (by positivity) (LemLin.linearCancellationConstant_nonneg d)

/-- Exact source normalization of the short-window linear cancellation estimate. -/
theorem integral_linearTimeSum_le_scaled_cancellation {d : ℕ} (D : SumintDatum d)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : r ≠ 0)
    (t : ℝ) (i : Fin D.S.I) {a b : ℝ} (hab : a ≤ b)
    (hshort : ((4*sourceHalfScale L γ δ)*(b-a))*‖r‖ ≤ 4*L) :
    (∫ s in Icc a b, ‖linearTimeSum D L γ δ p ν r t i s‖) ≤
      δ⁻¹*scaledLinearConstant d*L^((d:ℝ)-2*γ)/‖r‖ := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hscale : 0 < sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  have hb := integral_linearTimeSum_le_cancellation D (by linarith : 1 ≤ 4*L)
    γ δ hscale p ν r hr t i hab hshort
  have hs := source_scale_inv_mul_nat_pow hLp (by norm_num : (0:ℝ) < 4) hδ
    (by norm_num : (0:ℝ) ≤ 4) γ d
  have hinv : ((4:ℝ)/2)⁻¹ = 1/2 := by norm_num
  apply hb.trans_eq
  calc
    _ = LemLin.linearCancellationConstant d*((4*sourceHalfScale L γ δ)⁻¹*(4*L)^d)/‖r‖ := by ring
    _ = _ := by rw [hs,hinv]; unfold scaledLinearConstant; ring

/-- Case (b): its external factor cancels the exact reciprocal momentum norm. -/
theorem norm_mul_integral_linearTimeSum_le {d : ℕ} (D : SumintDatum d)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : r ≠ 0)
    (t : ℝ) (i : Fin D.S.I) {a b : ℝ} (hab : a ≤ b)
    (hshort : ((4*sourceHalfScale L γ δ)*(b-a))*‖r‖ ≤ 4*L) :
    ‖r‖*(∫ s in Icc a b, ‖linearTimeSum D L γ δ p ν r t i s‖) ≤
      δ⁻¹*scaledLinearConstant d*L^((d:ℝ)-2*γ) := by
  have hb := integral_linearTimeSum_le_scaled_cancellation D hL hδ γ p ν r hr t i hab hshort
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg r)).trans_eq (by
    rw [mul_comm,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hr)])

/-- F23: the lattice momentum lower bound gives the second linear branch needed in case (d). -/
theorem integral_linearTimeSum_le_f23 {d : ℕ} (D : SumintDatum d)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (hr : 1/L ≤ ‖r‖) (t : ℝ) (i : Fin D.S.I) {a b : ℝ} (hab : a ≤ b)
    (hshort : ((4*sourceHalfScale L γ δ)*(b-a))*‖r‖ ≤ 4*L) :
    (∫ s in Icc a b, ‖linearTimeSum D L γ δ p ν r t i s‖) ≤
      δ⁻¹*scaledLinearConstant d*L^((d:ℝ)+1-2*γ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hnp : 0 < ‖r‖ := (one_div_pos.mpr hLp).trans_le hr
  have hni : ‖r‖⁻¹ ≤ L := by
    rw [← one_div,div_le_iff₀ hnp]
    have hm := (div_le_iff₀ hLp).mp hr
    nlinarith only [hm]
  have hb := integral_linearTimeSum_le_scaled_cancellation D hL hδ γ p ν r
    (norm_pos_iff.mp hnp) t i hab hshort
  have hp : L^((d:ℝ)-2*γ)*L = L^((d:ℝ)+1-2*γ) := by
    calc
      _ = L^((d:ℝ)-2*γ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  calc
    _ ≤ δ⁻¹*scaledLinearConstant d*L^((d:ℝ)-2*γ)/‖r‖ := hb
    _ = (δ⁻¹*scaledLinearConstant d*L^((d:ℝ)-2*γ))*‖r‖⁻¹ := div_eq_mul_inv _ _
    _ ≤ (δ⁻¹*scaledLinearConstant d*L^((d:ℝ)-2*γ))*L :=
      mul_le_mul_of_nonneg_left hni (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδ.le) (scaledLinearConstant_nonneg d))
        (Real.rpow_nonneg hLp.le _))
    _ = _ := by rw [mul_assoc,mul_assoc,hp]; ring

end WaveTurbulence.SumintPar

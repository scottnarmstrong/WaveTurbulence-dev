/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairKernels
public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Integrability of the negative-regularity endpoint kernel

Distribute the max-bracket loss equally among the three coordinates.
Each scalar inverse bracket then has exponent strictly greater than one,
so the exact product endpoint majorant is integrable.
-/

public section

open MeasureTheory Finset

namespace WaveTurbulence.Sumint

/-- Inverse scalar bracket powers are integrable for all real exponents greater than one. -/
theorem integrable_scalarBracket_rpow {p : ℝ} (hp : 1 < p) :
    Integrable (fun s : ℝ => scalarBracket s^(-p)) := by
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := p) (by simpa using hp)
  apply hi.congr
  filter_upwards [] with s
  rw [Real.norm_eq_abs, sq_abs]
  unfold scalarBracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1+s^2)]
  congr 1
  ring

/-- The scalar max-bracket loss dominates one third of that loss in each coordinate. -/
theorem negative_endpoint_kernel_le {ε : ℝ} (hε : 0 ≤ ε) (ξ : Fin 3 → ℝ) :
    Fourier.timeBracket ξ^(-ε) * (∏ j, 1/scalarBracket (ξ j)) ≤
      ∏ j, scalarBracket (ξ j)^(-1-ε/3) := by
  have hb (j : Fin 3) : 0 < scalarBracket (ξ j) := zero_lt_one.trans_le (one_le_scalarBracket _)
  have hp (j : Fin 3) : Fourier.timeBracket ξ^(-ε/3) ≤ scalarBracket (ξ j)^(-ε/3) :=
    Real.rpow_le_rpow_of_nonpos (hb j) (Fourier.bracket_le_timeBracket ξ j) (by linarith)
  have he : (∏ _j : Fin 3, Fourier.timeBracket ξ^(-ε/3)) = Fourier.timeBracket ξ^(-ε) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_mul_natCast (Fourier.timeBracket_pos ξ).le]
    congr 1
    norm_num
  have hprod : Fourier.timeBracket ξ^(-ε) ≤ ∏ j, scalarBracket (ξ j)^(-ε/3) := by
    rw [← he]
    exact Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le _)
      (fun j _ => hp j)
  calc
    _ ≤ (∏ j, scalarBracket (ξ j)^(-ε/3)) * (∏ j, 1/scalarBracket (ξ j)) :=
      mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg (fun j _ => div_nonneg (by norm_num) (hb j).le))
    _ = ∏ j, scalarBracket (ξ j)^(-ε/3) * (1/scalarBracket (ξ j)) := (Finset.prod_mul_distrib).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      have hi : 1/scalarBracket (ξ j) = scalarBracket (ξ j)^(-1 : ℝ) := by
        rw [Real.rpow_neg_one, one_div]
      rw [hi, ← Real.rpow_add (hb j)]
      congr 1
      ring

/-- The exact max-weighted three-endpoint majorant is integrable at every negative regularity. -/
theorem integrable_negative_endpoint_kernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ξ : Fin 3 → ℝ => Fourier.timeBracket ξ^(-ε) *
      ∏ j, 1/scalarBracket (ξ j)) := by
  have hi : Integrable (fun ξ : Fin 3 → ℝ => ∏ j, scalarBracket (ξ j)^(-1-ε/3)) := by
    have hs := integrable_scalarBracket_rpow (p := 1+ε/3) (by linarith)
    have hp := Integrable.fintype_prod (μ := fun _ : Fin 3 => (volume : Measure ℝ)) (fun _ => hs)
    simpa only [volume_pi, neg_add, neg_div, sub_eq_add_neg] using hp
  have hc : Continuous (fun ξ : Fin 3 → ℝ => Fourier.timeBracket ξ^(-ε) *
      ∏ j, 1/scalarBracket (ξ j)) := by
    apply Continuous.mul
    · exact (Fourier.timeBracket_continuous 3).rpow_const
        (fun ξ => Or.inl (Fourier.timeBracket_pos ξ).ne')
    · apply continuous_finsetProd
      intro j _
      apply Continuous.div continuous_const
      · unfold scalarBracket
        fun_prop
      · intro ξ
        exact (zero_lt_one.trans_le (one_le_scalarBracket (ξ j))).ne'
  apply hi.mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro ξ
  have hn : 0 ≤ Fourier.timeBracket ξ^(-ε) * ∏ j, 1/scalarBracket (ξ j) :=
    mul_nonneg (Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le _) (Finset.prod_nonneg
      (fun j _ => div_nonneg (by norm_num) (zero_le_one.trans (one_le_scalarBracket _))))
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact negative_endpoint_kernel_le hε.le ξ

end WaveTurbulence.Sumint

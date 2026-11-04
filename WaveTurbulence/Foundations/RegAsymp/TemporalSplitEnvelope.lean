/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FrequencySplit
public import WaveTurbulence.Foundations.ClassJR.MCSRep

/-! # Integrating the actual low/high temporal-frequency majorant -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- J3's two-frequency weight in the real convention used by the split. -/
theorem wL_eq_ofReal_frequency_weight (a : ℝ) (lam : ℝ × ℝ) :
    wL a lam = ENNReal.ofReal ((1+|lam.1|+|lam.2|)^a) := by
  have he : ENNReal.ofReal (1+|lam.1|+|lam.2|) = 1+‖lam.1‖ₑ+‖lam.2‖ₑ := by
    rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ENNReal.ofReal_add (by norm_num : 0 ≤ (1:ℝ)) (abs_nonneg _),ENNReal.ofReal_one]
    simp only [← ofReal_norm,Real.norm_eq_abs]
  rw [wL,← he,ENNReal.ofReal_rpow_of_pos (by positivity)]

/-- The single common envelope uses the sharp bound on low frequencies
and the derivative-only crude bound on high frequencies. -/
@[expose] def temporalSplitEnvelope (L σ η : ℝ) (gD gM : (ℝ × ℝ) → ℝ) (lam : ℝ × ℝ) : ℝ :=
  min (gD lam) (L^(-σ+η)*gM lam)

/-- The common envelope is measurable before taking a momentum supremum. -/
theorem measurable_temporalSplitEnvelope (L σ η : ℝ) {gD gM : (ℝ × ℝ) → ℝ}
    (hmD : Measurable gD) (hmM : Measurable gM) :
    Measurable (temporalSplitEnvelope L σ η gD gM) :=
  hmD.min (measurable_const.mul hmM)

/-- The full η-weighted mass has exactly the source remainder rate,
using J3's distinct weak and strong temporal weights. -/
theorem lintegral_temporalSplitEnvelope_le {L σ η : ℝ} (hL : 1 ≤ L)
    (hσ : σ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ 1/20)
    {gD gM : (ℝ × ℝ) → ℝ} (hmM : Measurable gM)
    (hpD : ∀ lam, 0 ≤ gD lam) (hpM : ∀ lam, 0 ≤ gM lam) :
    (∫⁻ lam : ℝ × ℝ, wL η lam*ENNReal.ofReal (temporalSplitEnvelope L σ η gD gM lam)) ≤
      ENNReal.ofReal (L^(-σ+2*η)) *
        ((∫⁻ lam : ℝ × ℝ, wL (η/4) lam*ENNReal.ofReal (gM lam)) +
          ∫⁻ lam : ℝ × ℝ, wL (1-η/8) lam*ENNReal.ofReal (gD lam)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpt (lam : ℝ × ℝ) : wL η lam*ENNReal.ofReal (temporalSplitEnvelope L σ η gD gM lam) ≤
      ENNReal.ofReal (L^(-σ+2*η)) *
        (wL (η/4) lam*ENNReal.ofReal (gM lam)+wL (1-η/8) lam*ENNReal.ofReal (gD lam)) := by
    let q : ℝ := 1+|lam.1|+|lam.2|
    have hq : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg lam.1,abs_nonneg lam.2]
    have hE : 0 ≤ temporalSplitEnvelope L σ η gD gM lam :=
      le_min (hpD lam) (mul_nonneg (Real.rpow_nonneg hL0.le _) (hpM lam))
    have hMD := hpM lam
    have hDD := hpD lam
    have hh := frequency_split_majorant hL hq hη0 hη hσ hE (hpD lam) (hpM lam)
      (min_le_left _ _) (min_le_right _ _)
    have he : ENNReal.ofReal (q^η*temporalSplitEnvelope L σ η gD gM lam) ≤
        ENNReal.ofReal (L^(-σ+2*η)*(q^(η/4)*gM lam+q^(1-η/8)*gD lam)) :=
      ENNReal.ofReal_le_ofReal hh
    simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ L^(-σ+2*η)),
      ENNReal.ofReal_add (by positivity : 0 ≤ q^(η/4)*gM lam) (by positivity : 0 ≤ q^(1-η/8)*gD lam),
      ENNReal.ofReal_mul (by positivity : 0 ≤ q^η),
      ENNReal.ofReal_mul (by positivity : 0 ≤ q^(η/4)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ q^(1-η/8))] at he
    simpa only [wL_eq_ofReal_frequency_weight,q] using he
  calc
    _ ≤ ∫⁻ lam : ℝ × ℝ, ENNReal.ofReal (L^(-σ+2*η)) *
        (wL (η/4) lam*ENNReal.ofReal (gM lam)+wL (1-η/8) lam*ENNReal.ofReal (gD lam)) :=
      lintegral_mono hpt
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (f := fun lam => wL (η/4) lam*ENNReal.ofReal (gM lam))
          ((measurable_wL _).mul hmM.ennreal_ofReal)
          (fun lam => wL (1-η/8) lam*ENNReal.ofReal (gD lam))]

end WaveTurbulence.RegAsymp

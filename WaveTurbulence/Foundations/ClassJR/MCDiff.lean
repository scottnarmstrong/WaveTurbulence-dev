/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCGR

/-!
# The difference loss (DH21 (differenceloss))

DH21 L1141–L1145. In Case 2 of Proposition 5.1 the Lemma 5.10 factors are
`Φ(ε α̃_j) = χ_∞(α̃_j)/(επiα̃_j)` at the translated variable `α̃_j = α_j + ε λ`, and DH21 writes
`Φ(ε α̃_j) = Φ(ε α_j) + [Φ(εα_j + λ) - Φ(εα_j)]`. The difference is integrable in `α_j`:
`∫ |Φ(εx + λ) - Φ(εx)| dx ≤ C log(2 + |λ|)`.

We prove the weighted form used for (maincoef2.5) with the DH23 weights,
`∫ (1+|x|)^{b'} |Φ(εx+λ) - Φ(εx)| dx ≤ C (1+|λ|)^{b'+δ}` for `b' + δ ≤ 1`, `δ > 0`
(`lintegral_weight_Dfun_le`), and the Gevrey bounds of the derivatives (`lintegral_Dfun_gev_le`).
The log of DH21 is replaced by an arbitrarily small power `δ`.
* Pointwise: `|Φ(y+λ) - Φ(y)| ≤ C (1+|λ|) / ((1+|y|)(1+|y+λ|))` (`abs_chiInvR_sub_le`).
* Integral: in each of the cases `|y| ≥ |y+λ|`, `|y| < |y+λ|`, one factor is `≳ (1+|λ|)`; the
  remaining pair integral has total exponent `1 + δ` (`lintegral_pair_gen_le`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Pointwise

theorem abs_chiInvR_le (x : ℝ) : |chiInvR x| ≤ CPhi := by
  have := norm_chiInvR_le x
  rwa [Complex.norm_real, Real.norm_eq_abs] at this

/-- **The pointwise difference bound**: `|χ_∞(y+λ)/(y+λ) - χ_∞(y)/y| ≤ C (1+|λ|)/((1+|y|)(1+|y+λ|))`. -/
theorem abs_chiInvR_sub_le (y lam : ℝ) :
    |chiInvR (y + lam) - chiInvR y| ≤
      (8 * CPhi + 4) * (1 + |lam|) / ((1 + |y|) * (1 + |y + lam|)) := by
  have hP : 0 < (1 + |y|) * (1 + |y + lam|) := by positivity
  have hCP := CPhi_nonneg
  rw [le_div_iff₀ hP]
  have hyl := abs_add_le y lam
  by_cases h1 : 1 ≤ |y|
  · by_cases h2 : 1 ≤ |y + lam|
    · have hy0 : y ≠ 0 := by intro h; rw [h, abs_zero] at h1; linarith
      have hyl0 : y + lam ≠ 0 := by intro h; rw [h, abs_zero] at h2; linarith
      rw [chiInvR_eq_inv h1, chiInvR_eq_inv h2]
      have hD : (y + lam)⁻¹ - y⁻¹ = -lam / (y * (y + lam)) := by
        field_simp
        ring
      rw [hD, abs_div, abs_neg, abs_mul]
      have hyp : 0 < |y| * |y + lam| := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hyp]
      have e1 : 1 + |y| ≤ 2 * |y| := by linarith
      have e2 : 1 + |y + lam| ≤ 2 * |y + lam| := by linarith
      have hl0 := abs_nonneg lam
      calc |lam| * ((1 + |y|) * (1 + |y + lam|)) ≤ |lam| * ((2 * |y|) * (2 * |y + lam|)) := by
            gcongr
        _ = 4 * |lam| * (|y| * |y + lam|) := by ring
        _ ≤ (8 * CPhi + 4) * (1 + |lam|) * (|y| * |y + lam|) := by
            have : 4 * |lam| ≤ (8 * CPhi + 4) * (1 + |lam|) := by nlinarith
            exact mul_le_mul_of_nonneg_right this hyp.le
    · rw [not_le] at h2
      have hb : |chiInvR (y + lam) - chiInvR y| ≤ 2 * CPhi := by
        have := abs_sub (chiInvR (y + lam)) (chiInvR y)
        linarith [abs_chiInvR_le (y + lam), abs_chiInvR_le y]
      have hP4 : (1 + |y|) * (1 + |y + lam|) ≤ 4 * (1 + |lam|) := by
        have : |y| ≤ |y + lam| + |lam| := by
          have h := abs_add_le (y + lam) (-lam)
          rwa [abs_neg, show y + lam + -lam = y by ring] at h
        nlinarith [abs_nonneg y, abs_nonneg (y + lam), abs_nonneg lam]
      calc |chiInvR (y + lam) - chiInvR y| * ((1 + |y|) * (1 + |y + lam|))
          ≤ (2 * CPhi) * (4 * (1 + |lam|)) := by
            apply mul_le_mul hb hP4 hP.le (by positivity)
        _ ≤ (8 * CPhi + 4) * (1 + |lam|) := by nlinarith [abs_nonneg lam]
  · rw [not_le] at h1
    have hb : |chiInvR (y + lam) - chiInvR y| ≤ 2 * CPhi := by
      have := abs_sub (chiInvR (y + lam)) (chiInvR y)
      linarith [abs_chiInvR_le (y + lam), abs_chiInvR_le y]
    have hP4 : (1 + |y|) * (1 + |y + lam|) ≤ 4 * (1 + |lam|) := by
      nlinarith [abs_nonneg y, abs_nonneg (y + lam), abs_nonneg lam]
    calc |chiInvR (y + lam) - chiInvR y| * ((1 + |y|) * (1 + |y + lam|))
        ≤ (2 * CPhi) * (4 * (1 + |lam|)) := by
          apply mul_le_mul hb hP4 hP.le (by positivity)
      _ ≤ (8 * CPhi + 4) * (1 + |lam|) := by nlinarith [abs_nonneg lam]

theorem norm_phiR_eq (x : ℝ) : ‖phiR x‖ = |chiInvR x| / π := by
  rw [phiR, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem norm_phiR_sub_le (y lam : ℝ) :
    ‖phiR (y + lam) - phiR y‖ ≤ (8 * CPhi + 4) * (1 + |lam|) / ((1 + |y|) * (1 + |y + lam|)) := by
  have e : phiR (y + lam) - phiR y = ((chiInvR (y + lam) - chiInvR y : ℝ) : ℂ) / (π * I) := by
    simp only [phiR]
    push_cast
    ring
  rw [e, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc |chiInvR (y + lam) - chiInvR y| / π ≤ |chiInvR (y + lam) - chiInvR y| :=
        div_le_self (abs_nonneg _) (by linarith [Real.two_le_pi])
    _ ≤ _ := abs_chiInvR_sub_le y lam


end Pointwise

section Integral

/-- The constant of the difference loss. -/
@[expose] noncomputable def CD (b' δ : ℝ) : ℝ := (8 * CPhi + 4) * 2 ^ (1 - b' - δ) * (2 * Ir (1 + δ))

theorem CD_nonneg (b' δ : ℝ) : 0 ≤ CD b' δ := by
  have := CPhi_nonneg
  have : 0 ≤ Ir (1 + δ) := ENNReal.toReal_nonneg
  unfold CD; positivity

/-- The pair bound behind the difference loss:
`(1+|y|)^{b'-1} (1+|y+λ|)^{-1} ≤ 2^{1-b'-δ} (1+|λ|)^{b'+δ-1} (T₁ + T₂)`. -/
theorem pair_split_le {b' δ : ℝ} (hbδ : b' + δ ≤ 1) (y lam : ℝ) :
    (1 + |y|) ^ (b' - 1) * (1 + |y + lam|) ^ (-(1 : ℝ)) ≤
      2 ^ (1 - b' - δ) * (1 + |lam|) ^ (b' + δ - 1) *
        ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ)) +
          (1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ))) := by
  set c : ℝ := b' + δ - 1 with hc
  have hc0 : c ≤ 0 := by linarith
  have hY0 : 0 < 1 + |y| := by positivity
  have hW0 : 0 < 1 + |y + lam| := by positivity
  have hL0 : 0 < 1 + |lam| := by positivity
  have hM : ((1 + |lam|) / 2) ^ c = 2 ^ (1 - b' - δ) * (1 + |lam|) ^ c := by
    rw [Real.div_rpow hL0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num), mul_comm]
    congr 2
    ring
  have hT1 : 0 ≤ (1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ)) := by positivity
  have hT2 : 0 ≤ (1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ)) := by positivity
  have hK : 0 ≤ 2 ^ (1 - b' - δ) * (1 + |lam|) ^ c := by positivity
  rcases le_or_gt |y + lam| |y| with h | h
  · have hl : (1 + |lam|) / 2 ≤ 1 + |y| := by
      have : |lam| ≤ |y| + |y + lam| := by
        have h' := abs_add_le (-y) (y + lam)
        rwa [abs_neg, show -y + (y + lam) = lam by ring] at h'
      linarith
    have e : (1 + |y|) ^ (b' - 1) = (1 + |y|) ^ c * (1 + |y|) ^ (-δ) := by
      rw [← Real.rpow_add hY0]; congr 1; ring
    have h1 : (1 + |y|) ^ c ≤ ((1 + |lam|) / 2) ^ c :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hl hc0
    calc (1 + |y|) ^ (b' - 1) * (1 + |y + lam|) ^ (-(1 : ℝ))
        = (1 + |y|) ^ c * ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) := by rw [e]; ring
      _ ≤ ((1 + |lam|) / 2) ^ c * ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) := by gcongr
      _ = 2 ^ (1 - b' - δ) * (1 + |lam|) ^ c *
            ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) := by rw [hM]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT2) hK
  · have hl : (1 + |lam|) / 2 ≤ 1 + |y + lam| := by
      have : |lam| ≤ |y| + |y + lam| := by
        have h' := abs_add_le (-y) (y + lam)
        rwa [abs_neg, show -y + (y + lam) = lam by ring] at h'
      linarith
    have e : (1 + |y + lam|) ^ (-(1 : ℝ)) = (1 + |y + lam|) ^ c * (1 + |y + lam|) ^ (-(b' + δ)) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have h1 : (1 + |y + lam|) ^ c ≤ ((1 + |lam|) / 2) ^ c :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hl hc0
    have e2 : (1 + |y|) ^ (b' - 1) = (1 + |y|) ^ (-(1 - b')) := by ring_nf
    calc (1 + |y|) ^ (b' - 1) * (1 + |y + lam|) ^ (-(1 : ℝ))
        = (1 + |y + lam|) ^ c * ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ))) := by
          rw [e, e2]; ring
      _ ≤ ((1 + |lam|) / 2) ^ c * ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ))) := by
          gcongr
      _ = 2 ^ (1 - b' - δ) * (1 + |lam|) ^ c *
            ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ))) := by rw [hM]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hT1) hK

/-- **The weighted difference loss** (DH21 (differenceloss) with the DH23 weights):
`∫ (1+|y|)^{b'} |Φ(y+λ) - Φ(y)| dy ≤ CD (1+|λ|)^{b'+δ}` for `0 ≤ b'`, `0 < δ`, `b' + δ ≤ 1`. -/
theorem lintegral_weight_phiR_sub_le {b' δ : ℝ} (hb' : 0 ≤ b') (hδ : 0 < δ) (hbδ : b' + δ ≤ 1)
    (lam : ℝ) :
    ∫⁻ y : ℝ, ((1 : ℝ≥0∞) + ‖y‖ₑ) ^ b' * ‖phiR (y + lam) - phiR y‖ₑ ≤
      ENNReal.ofReal (CD b' δ * (1 + |lam|) ^ (b' + δ)) := by
  have hCP := CPhi_nonneg
  set K : ℝ := (8 * CPhi + 4) * (1 + |lam|) * (2 ^ (1 - b' - δ) * (1 + |lam|) ^ (b' + δ - 1))
    with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ y : ℝ, ((1 : ℝ≥0∞) + ‖y‖ₑ) ^ b' * ‖phiR (y + lam) - phiR y‖ₑ ≤
      ENNReal.ofReal K * (ENNReal.ofReal ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) +
        ENNReal.ofReal ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ)))) := by
    intro y
    have hY0 : 0 < 1 + |y| := by positivity
    have hW0 : 0 < 1 + |y + lam| := by positivity
    rw [one_add_enorm_rpow_eq, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 + |y|) ^ b' * ‖phiR (y + lam) - phiR y‖
        ≤ (1 + |y|) ^ b' * ((8 * CPhi + 4) * (1 + |lam|) / ((1 + |y|) * (1 + |y + lam|))) :=
          mul_le_mul_of_nonneg_left (norm_phiR_sub_le y lam) (by positivity)
      _ = (8 * CPhi + 4) * (1 + |lam|) * ((1 + |y|) ^ (b' - 1) * (1 + |y + lam|) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_sub_one hY0.ne', Real.rpow_neg_one]
          field_simp
      _ ≤ (8 * CPhi + 4) * (1 + |lam|) * (2 ^ (1 - b' - δ) * (1 + |lam|) ^ (b' + δ - 1) *
            ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ)) +
              (1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ)))) :=
          mul_le_mul_of_nonneg_left (pair_split_le hbδ y lam) (by positivity)
      _ = K * ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ)) +
            (1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ))) := by rw [hK]; ring
  have hm1 : Measurable fun y : ℝ =>
      ENNReal.ofReal ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) := by fun_prop
  have hIr : 0 ≤ Ir (1 + δ) := ENNReal.toReal_nonneg
  calc ∫⁻ y : ℝ, ((1 : ℝ≥0∞) + ‖y‖ₑ) ^ b' * ‖phiR (y + lam) - phiR y‖ₑ
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal K *
          (ENNReal.ofReal ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ))) +
          ENNReal.ofReal ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal K *
          ((∫⁻ y : ℝ, ENNReal.ofReal ((1 + |y|) ^ (-δ) * (1 + |y + lam|) ^ (-(1 : ℝ)))) +
          ∫⁻ y : ℝ, ENNReal.ofReal ((1 + |y|) ^ (-(1 - b')) * (1 + |y + lam|) ^ (-(b' + δ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (Ir (1 + δ)) + ENNReal.ofReal (Ir (1 + δ))) := by
        gcongr
        · refine (lintegral_pair_gen_le hδ.le zero_le_one (by linarith) lam).trans_eq ?_
          congr 2; ring
        · refine (lintegral_pair_gen_le (by linarith) (by linarith) (by linarith) lam).trans_eq ?_
          congr 2; ring
    _ = ENNReal.ofReal (CD b' δ * (1 + |lam|) ^ (b' + δ)) := by
        rw [← ENNReal.ofReal_add hIr hIr, ← ENNReal.ofReal_mul hK0]
        congr 1
        have hL0 : 0 < 1 + |lam| := by positivity
        have e : (1 + |lam|) * (1 + |lam|) ^ (b' + δ - 1) = (1 + |lam|) ^ (b' + δ) := by
          have h := Real.rpow_add hL0 1 (b' + δ - 1)
          rw [Real.rpow_one] at h
          rw [← h]; congr 1; ring
        rw [hK, CD]
        calc (8 * CPhi + 4) * (1 + |lam|) * (2 ^ (1 - b' - δ) * (1 + |lam|) ^ (b' + δ - 1)) *
              (Ir (1 + δ) + Ir (1 + δ))
            = (8 * CPhi + 4) * 2 ^ (1 - b' - δ) * (2 * Ir (1 + δ)) *
              ((1 + |lam|) * (1 + |lam|) ^ (b' + δ - 1)) := by ring
          _ = _ := by rw [e]


/-- **The difference symbol** `Φ(εx + λ) - Φ(εx)`. -/
@[expose] noncomputable def Dfun (ε : ℤ) (lam x : ℝ) : ℂ := phiR (ε * x + lam) - phiR (ε * x)

theorem contDiff_Dfun (ε : ℤ) (lam : ℝ) : ContDiff ℝ ∞ (Dfun ε lam) :=
  (contDiff_phiR.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).sub
    (contDiff_phiR.comp (contDiff_const.mul contDiff_id))

theorem measurable_Dfun (ε : ℤ) : Measurable fun p : ℝ × ℝ => Dfun ε p.1 p.2 := by
  unfold Dfun
  exact (contDiff_phiR.continuous.measurable.comp (by fun_prop)).sub
    (contDiff_phiR.continuous.measurable.comp (by fun_prop))

/-- **The weighted difference loss with a sign**:
`∫ (1+|x|)^{b'} |Φ(εx+λ) - Φ(εx)| dx ≤ CD (1+|λ|)^{b'+δ}`. -/
theorem lintegral_weight_Dfun_le {b' δ : ℝ} (hb' : 0 ≤ b') (hδ : 0 < δ) (hbδ : b' + δ ≤ 1)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (lam : ℝ) :
    ∫⁻ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ‖Dfun ε lam x‖ₑ ≤
      ENNReal.ofReal (CD b' δ * (1 + |lam|) ^ (b' + δ)) := by
  rcases hε with h | h
  · simp only [Dfun, h, Int.cast_one, one_mul]
    exact lintegral_weight_phiR_sub_le hb' hδ hbδ lam
  · have e : ∀ x : ℝ, ((1 : ℝ≥0∞) + ‖x‖ₑ) ^ b' * ‖Dfun ε lam x‖ₑ =
        (fun y : ℝ => ((1 : ℝ≥0∞) + ‖y‖ₑ) ^ b' * ‖phiR (y + lam) - phiR y‖ₑ) (-x) := fun x => by
      simp [Dfun, h]
    simp_rw [e]
    rw [lintegral_neg_eq_self (fun y : ℝ => ((1 : ℝ≥0∞) + ‖y‖ₑ) ^ b' * ‖phiR (y + lam) - phiR y‖ₑ)]
    exact lintegral_weight_phiR_sub_le hb' hδ hbδ lam

theorem norm_iteratedDeriv_phiR_le_chi (k : ℕ) (y : ℝ) :
    ‖iteratedDeriv k phiR y‖ ≤ ‖iteratedDeriv k chiInvR y‖ := by
  have h : phiR = ((π : ℂ) * I)⁻¹ • (Complex.ofRealCLM ∘ chiInvR) := by
    funext x; simp [phiR, div_eq_inv_mul]
  have hc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ chiInvR) :=
    Complex.ofRealCLM.contDiff.comp contDiff_chiInvR
  have h2 : ‖iteratedDeriv k (Complex.ofRealCLM ∘ chiInvR) y‖ = ‖iteratedDeriv k chiInvR y‖ :=
    norm_iteratedDeriv_ofReal contDiff_chiInvR k y
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h,
    iteratedFDeriv_const_smul_apply (hc.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, h2]
  have h1 : ‖((π : ℂ) * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  calc ‖((π : ℂ) * I)⁻¹‖ * ‖iteratedDeriv k chiInvR y‖ ≤ 1 * ‖iteratedDeriv k chiInvR y‖ := by
        gcongr
    _ = _ := one_mul _

/-- For `k ≥ 1`, `|∂^k Φ(y)| ≤ (4C_Φ + 4) A_χ^k (2k)! (1+|y|)^{-2}`. -/
theorem norm_iteratedDeriv_phiR_le_sq {k : ℕ} (hk : 1 ≤ k) (y : ℝ) :
    ‖iteratedDeriv k phiR y‖ ≤
      (4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) * (1 + |y|) ^ (-(2 : ℝ)) := by
  refine (norm_iteratedDeriv_phiR_le_chi k y).trans ?_
  have hY : 0 < 1 + |y| := by positivity
  have hA : 1 ≤ Achi ^ k := one_le_pow₀ (by linarith [two_le_Achi])
  have hf : (k.factorial : ℝ) ≤ ((2 * k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hCP := CPhi_nonneg
  have hsq : (1 + |y|) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hY.le]; norm_cast
  rw [hsq]
  rcases le_or_gt |y| 1 with h | h
  · have h4 : (1 + |y|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg y]
    have hb := norm_iteratedDeriv_chiInvR_le k y
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖iteratedDeriv k chiInvR y‖ * (1 + |y|) ^ 2
        ≤ (CPhi * Achi ^ k * ((2 * k).factorial : ℝ)) * 4 := by
          apply mul_le_mul hb h4 (by positivity) (by positivity)
      _ ≤ (4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) := by
          have : 0 ≤ Achi ^ k * ((2 * k).factorial : ℝ) := by positivity
          nlinarith
  · rw [iteratedDeriv_chiInvR_of_lt h k, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Real.norm_natCast, norm_inv, norm_pow, Real.norm_eq_abs]
    have hy1 : 1 ≤ |y| := h.le
    have hpow : |y| ^ 2 ≤ |y| ^ (k + 1) := pow_le_pow_right₀ hy1 (by omega)
    have h2 : (1 + |y|) ^ 2 ≤ 4 * |y| ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (k.factorial : ℝ) * (1 + |y|) ^ 2 ≤ (k.factorial : ℝ) * (4 * |y| ^ (k + 1)) := by
          gcongr; linarith
      _ ≤ (4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) * |y| ^ (k + 1) := by
          have h0 : 0 ≤ |y| ^ (k + 1) := by positivity
          have : (k.factorial : ℝ) * 4 ≤ (4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) := by
            have : (k.factorial : ℝ) ≤ Achi ^ k * ((2 * k).factorial : ℝ) := by
              calc (k.factorial : ℝ) ≤ 1 * ((2 * k).factorial : ℝ) := by rw [one_mul]; exact hf
                _ ≤ _ := by gcongr
            nlinarith
          nlinarith

/-- `∫ (1+|εx+λ|)^{-r} dx = Ir(r)`. -/
theorem lintegral_decay_affine {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (lam r : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + |ε * x + lam|) ^ (-r)) =
      ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-r)) := by
  rcases hε with h | h
  · simp only [h, Int.cast_one, one_mul]
    exact lintegral_add_right_eq_self (fun u : ℝ => ENNReal.ofReal ((1 + |u|) ^ (-r))) lam
  · have e : ∀ x : ℝ, ENNReal.ofReal ((1 + |ε * x + lam|) ^ (-r)) =
        (fun u : ℝ => ENNReal.ofReal ((1 + |u + lam|) ^ (-r))) (-x) := fun x => by
      simp [h]
    simp_rw [e]
    rw [lintegral_neg_eq_self (fun u : ℝ => ENNReal.ofReal ((1 + |u + lam|) ^ (-r)))]
    exact lintegral_add_right_eq_self (fun u : ℝ => ENNReal.ofReal ((1 + |u|) ^ (-r))) lam

/-- The Gevrey constant of the difference symbol. -/
@[expose] noncomputable def CDg (δ : ℝ) : ℝ := CD 0 δ + 2 * (4 * CPhi + 4) * Ir 2

theorem CDg_nonneg (δ : ℝ) : 0 ≤ CDg δ := by
  have := CD_nonneg 0 δ; have := CPhi_nonneg; have := Ir2_nonneg
  unfold CDg; positivity

/-- **The Gevrey bounds of the difference symbol** (for (maincoef2)):
`∫ |∂_x^k (Φ(εx+λ) - Φ(εx))| dx ≤ gev (CDg δ) A_χ k (1+|λ|)^δ` for `0 < δ ≤ 1`. -/
theorem lintegral_Dfun_gev_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (lam : ℝ) (k : ℕ) :
    ∫⁻ x : ℝ, ‖iteratedDeriv k (Dfun ε lam) x‖ₑ ≤
      gev (CDg δ) Achi k * ((1 : ℝ≥0∞) + ‖lam‖ₑ) ^ δ := by
  have hCP := CPhi_nonneg
  have hδ0 : 0 ≤ δ := hδ.le
  have hL1 : (1 : ℝ≥0∞) ≤ ((1 : ℝ≥0∞) + ‖lam‖ₑ) ^ δ := ENNReal.one_le_rpow le_self_add hδ
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [iteratedDeriv_zero]
    have h := lintegral_weight_Dfun_le (b' := 0) le_rfl hδ (by linarith) hε lam
    simp only [ENNReal.rpow_zero, one_mul, zero_add] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (CD_nonneg 0 δ), ← one_add_enorm_rpow_eq, gev_zero_eq]
    gcongr
    unfold CDg
    have := Ir2_nonneg
    nlinarith
  · -- `k ≥ 1`: both terms are integrable
    have hL : ∀ c : ℝ, ContDiff ℝ ∞ fun x : ℝ => phiR (ε * x + c) := fun c =>
      contDiff_phiR.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
    have hεL : ‖(ε : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
      refine (norm_smul_le (ε : ℝ) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
      have hn : ‖(ε : ℝ)‖ = 1 := by rcases hε with h | h <;> simp [h]
      rw [hn, one_mul]
      exact ContinuousLinearMap.norm_id_le
    have hpt : ∀ x : ℝ, ‖iteratedDeriv k (Dfun ε lam) x‖ₑ ≤
        ‖iteratedDeriv k phiR (ε * x + lam)‖ₑ + ‖iteratedDeriv k phiR (ε * x + 0)‖ₑ := by
      intro x
      have e : Dfun ε lam = (fun x : ℝ => phiR (ε * x + lam)) - fun x : ℝ => phiR (ε * x + 0) := by
        funext x; simp [Dfun]
      rw [← ofReal_norm, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, e,
        iteratedFDeriv_sub_apply ((hL lam).contDiffAt.of_le (by exact_mod_cast le_top))
          ((hL 0).contDiffAt.of_le (by exact_mod_cast le_top)), ofReal_norm]
      refine (enorm_sub_le).trans (add_le_add ?_ ?_)
      · exact enorm_iteratedFDeriv_scalar_le contDiff_phiR
          ((ε : ℝ) • ContinuousLinearMap.id ℝ ℝ) hεL lam x k
      · exact enorm_iteratedFDeriv_scalar_le contDiff_phiR
          ((ε : ℝ) • ContinuousLinearMap.id ℝ ℝ) hεL 0 x k
    have hb : ∀ c : ℝ, ∫⁻ x : ℝ, ‖iteratedDeriv k phiR (ε * x + c)‖ₑ ≤
        ENNReal.ofReal ((4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) * Ir 2) := by
      intro c
      calc ∫⁻ x : ℝ, ‖iteratedDeriv k phiR (ε * x + c)‖ₑ
          ≤ ∫⁻ x : ℝ, ENNReal.ofReal ((4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ)) *
              ENNReal.ofReal ((1 + |ε * x + c|) ^ (-(2 : ℝ))) := by
            refine lintegral_mono fun x => ?_
            rw [← ENNReal.ofReal_mul (by have := Achi_nonneg; positivity), ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_iteratedDeriv_phiR_le_sq hk _)
        _ = ENNReal.ofReal ((4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ)) *
              ENNReal.ofReal (Ir 2) := by
            rw [lintegral_const_mul _ (by fun_prop), lintegral_decay_affine hε c 2,
              lintegral_Ir_eq (by norm_num)]
        _ = _ := by rw [← ENNReal.ofReal_mul (by have := Achi_nonneg; positivity)]
    have hm1 : Measurable fun x : ℝ => ‖iteratedDeriv k phiR (ε * x + lam)‖ₑ :=
      ((contDiff_phiR.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp
        (by fun_prop : Continuous fun x : ℝ => (ε : ℝ) * x + lam)).measurable.enorm
    calc ∫⁻ x : ℝ, ‖iteratedDeriv k (Dfun ε lam) x‖ₑ
        ≤ ∫⁻ x : ℝ, (‖iteratedDeriv k phiR (ε * x + lam)‖ₑ +
            ‖iteratedDeriv k phiR (ε * x + 0)‖ₑ) := lintegral_mono hpt
      _ = (∫⁻ x : ℝ, ‖iteratedDeriv k phiR (ε * x + lam)‖ₑ) +
            ∫⁻ x : ℝ, ‖iteratedDeriv k phiR (ε * x + 0)‖ₑ := lintegral_add_left hm1 _
      _ ≤ ENNReal.ofReal ((4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) * Ir 2) +
            ENNReal.ofReal ((4 * CPhi + 4) * Achi ^ k * ((2 * k).factorial : ℝ) * Ir 2) :=
          add_le_add (hb lam) (hb 0)
      _ ≤ gev (CDg δ) Achi k * 1 := by
          rw [mul_one, ← ENNReal.ofReal_add (by have := Achi_nonneg; have := Ir2_nonneg; positivity)
            (by have := Achi_nonneg; have := Ir2_nonneg; positivity), gev]
          refine ENNReal.ofReal_le_ofReal ?_
          have := CD_nonneg 0 δ; have := Ir2_nonneg
          have hAk : 0 ≤ Achi ^ k * ((2 * k).factorial : ℝ) := by
            have := Achi_nonneg; positivity
          unfold CDg
          nlinarith
      _ ≤ _ := mul_le_mul' le_rfl hL1

end Integral

end WaveTurbulence.ClassJR

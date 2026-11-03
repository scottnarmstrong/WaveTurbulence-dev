/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.FrequencyEnvelope

/-!
# Convolution of finite frequency envelopes

Products in time add frequency centres. The Cauchy envelope pays a fixed
factor `4π`, independently of the centres and of the number of packets.
-/

public section

open MeasureTheory
open scoped ENNReal Convolution

namespace WaveTurbulence.Analysis

private theorem lintegral_two_centres_le (a b t : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (s - a)) *
      ENNReal.ofReal (cauchyWeight (t - s - b))) ≤
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (cauchyWeight (t - (a + b))) := by
  have heq (s : ℝ) : ENNReal.ofReal (cauchyWeight (s - a)) *
      ENNReal.ofReal (cauchyWeight (t - s - b)) =
      (fun y : ℝ => ENNReal.ofReal (cauchyWeight (t - (a + b) - y)) *
        ENNReal.ofReal (cauchyWeight y)) (s - a) := by
    dsimp only
    rw [show t - (a + b) - (s - a) = t - s - b by ring, mul_comm]
  simp_rw [heq]
  rw [lintegral_sub_right_eq_self (fun y : ℝ => ENNReal.ofReal (cauchyWeight (t - (a + b) - y)) *
    ENNReal.ofReal (cauchyWeight y)) a]
  exact lintegral_cauchyWeight_mul_le _

/-- The integral of the product of two packets is another finite packet
with added centres. -/
theorem lintegral_frequencyEnvelope_mul_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (w : ι → ℝ≥0∞) (d : κ → ℝ) (v : κ → ℝ≥0∞) (t : ℝ) :
    (∫⁻ s : ℝ, frequencyEnvelope c w s * frequencyEnvelope d v (t - s)) ≤
      ENNReal.ofReal (4 * Real.pi) * frequencyEnvelope
        (fun p : ι × κ => c p.1 + d p.2) (fun p => w p.1 * v p.2) t := by
  unfold frequencyEnvelope
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [lintegral_finsetSum _ (by intro i hi; unfold cauchyWeight; fun_prop)]
  have hh (i : ι) :
      (∫⁻ s : ℝ, ∑ j, w i * ENNReal.ofReal (cauchyWeight (s - c i)) *
        (v j * ENNReal.ofReal (cauchyWeight (t - s - d j)))) ≤
      ∑ j, ENNReal.ofReal (4 * Real.pi) * (w i * v j) *
        ENNReal.ofReal (cauchyWeight (t - (c i + d j))) := by
    rw [lintegral_finsetSum _ (by intro j hj; unfold cauchyWeight; fun_prop)]
    apply Finset.sum_le_sum
    intro j hj
    have heq (s : ℝ) : w i * ENNReal.ofReal (cauchyWeight (s - c i)) *
        (v j * ENNReal.ofReal (cauchyWeight (t - s - d j))) =
        (w i * v j) * (ENNReal.ofReal (cauchyWeight (s - c i)) *
          ENNReal.ofReal (cauchyWeight (t - s - d j))) := by ring
    simp_rw [heq]
    rw [lintegral_const_mul _ (by unfold cauchyWeight; fun_prop)]
    convert mul_le_mul' (le_refl (w i * v j)) (lintegral_two_centres_le (c i) (d j) t) using 1; ring
  calc
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal (4 * Real.pi) * (w i * v j) *
        ENNReal.ofReal (cauchyWeight (t - (c i + d j))) := Finset.sum_le_sum fun i _ => hh i
    _ = _ := by rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring

/-- The actual convolution satisfies the packet estimate at every
frequency, including where integrability has not yet been established. -/
theorem enorm_convolution_le_frequencyEnvelope {ι κ : Type*} [Fintype ι] [Fintype κ]
    {g h : ℝ → ℂ} (c : ι → ℝ) (w : ι → ℝ≥0∞) (d : κ → ℝ) (v : κ → ℝ≥0∞)
    (hg : ∀ s, ‖g s‖ₑ ≤ frequencyEnvelope c w s)
    (hh : ∀ s, ‖h s‖ₑ ≤ frequencyEnvelope d v s) (t : ℝ) :
    ‖(g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) t‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi) * frequencyEnvelope
        (fun p : ι × κ => c p.1 + d p.2) (fun p => w p.1 * v p.2) t := by
  rw [convolution_def]
  calc
    _ ≤ ∫⁻ s : ℝ, ‖g s * h (t - s)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s : ℝ, frequencyEnvelope c w s * frequencyEnvelope d v (t - s) := by
      apply lintegral_mono
      intro s
      dsimp only
      rw [enorm_mul]
      exact mul_le_mul' (hg s) (hh (t - s))
    _ ≤ _ := lintegral_frequencyEnvelope_mul_le c w d v t

/-- The norm of a synthesized packet is bounded by its total mass. -/
theorem enorm_spectralSynthesis_le_frequencyEnvelope {ι : Type*} [Fintype ι]
    {g : ℝ → ℂ} (c : ι → ℝ) (w : ι → ℝ≥0∞)
    (hg : ∀ s, ‖g s‖ₑ ≤ frequencyEnvelope c w s) (t : ℝ) :
    ‖spectralSynthesis g t‖ₑ ≤ (∑ i, w i) * ENNReal.ofReal Real.pi := by
  rw [spectralSynthesis_eq_integral]
  calc
    _ ≤ ∫⁻ s : ℝ, ‖timePhase t s * g s‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s : ℝ, frequencyEnvelope c w s := by
      apply lintegral_mono
      intro s
      dsimp only
      rw [enorm_mul, ← ofReal_norm, norm_timePhase, ENNReal.ofReal_one, one_mul]
      exact hg s
    _ = _ := lintegral_frequencyEnvelope c w

end WaveTurbulence.Analysis

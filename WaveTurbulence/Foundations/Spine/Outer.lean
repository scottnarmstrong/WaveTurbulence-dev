/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Corner
/-! # Outer time integrals of a rung (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open MeasureTheory Set

/-- Same layer: a uniform bound integrates to the box length times the bound. -/
theorem outer_same {G : ℝ → ℝ} {v w B : ℝ} (hvw : v ≤ w) (hG0 : ∀ t, 0 ≤ G t)
    (hb : ∀ t ∈ Icc v w, G t ≤ B) :
    (∫ t in Icc v w, G t) ≤ (w - v) * B := by
  have hB : (∫ _t in Icc v w, B) = (w - v) * B := by
    simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hvw)]
  rw [← hB]
  refine integral_mono_of_nonneg (ae_of_all _ hG0)
    (integrableOn_const (μ := volume) (s := Icc v w) (by simp [Real.volume_Icc])) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hb t ht

/-- Different layers: the distance weight integrates to `c'⁻¹`. -/
theorem outer_diff {d : ℕ} (hd : 3 ≤ d) {c' v w P Q : ℝ} (hc' : 0 < c') (hvw : v ≤ w)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (flag : Prop) [Decidable flag] {G : ℝ → ℝ} (hG0 : ∀ t, 0 ≤ G t)
    (hb : ∀ t ∈ Icc v w, G t ≤ P + Q * (1 + (if flag then c' * (t - v) else c' * (w - t))) ^
      (-((d : ℝ) - 1))) :
    (∫ t in Icc v w, G t) ≤ (w - v) * P + Q * c'⁻¹ := by
  set mfun : ℝ → ℝ := fun t => if flag then c' * (t - v) else c' * (w - t) with hmfun
  have hpos : ∀ t ∈ Icc v w, 0 < 1 + mfun t := by
    intro t ht
    have : 0 ≤ mfun t := by
      rw [hmfun]; dsimp only
      split_ifs
      · exact mul_nonneg hc'.le (by linarith [ht.1])
      · exact mul_nonneg hc'.le (by linarith [ht.2])
    linarith
  have hgcont : ContinuousOn (fun t : ℝ => (1 + mfun t) ^ (-((d : ℝ) - 1))) (Icc v w) := by
    refine ContinuousOn.rpow_const ?_ (fun t ht => Or.inl (hpos t ht).ne')
    rw [hmfun]
    by_cases hf : flag
    · simp only [hf, if_true]; fun_prop
    · simp only [hf, if_false]; fun_prop
  have hgint : IntegrableOn (fun t : ℝ => (1 + mfun t) ^ (-((d : ℝ) - 1))) (Icc v w) :=
    hgcont.integrableOn_Icc
  have hdecay : (∫ t in Icc v w, (1 + mfun t) ^ (-((d : ℝ) - 1))) ≤ c'⁻¹ := by
    by_cases hf : flag
    · have := outer_decay hd hc' hvw
      simpa only [hmfun, hf, if_true] using this
    · have := outer_decay_rev hd hc' hvw
      simpa only [hmfun, hf, if_false] using this
  have hRHS : (∫ t in Icc v w, (P + Q * (1 + mfun t) ^ (-((d : ℝ) - 1)))) =
      (w - v) * P + Q * ∫ t in Icc v w, (1 + mfun t) ^ (-((d : ℝ) - 1)) := by
    rw [integral_add (integrableOn_const (μ := volume) (s := Icc v w) (by simp [Real.volume_Icc]))
      (hgint.const_mul Q), integral_const_mul]
    simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hvw), mul_comm]
  calc (∫ t in Icc v w, G t) ≤ ∫ t in Icc v w, (P + Q * (1 + mfun t) ^ (-((d : ℝ) - 1))) := by
        refine integral_mono_of_nonneg (ae_of_all _ hG0)
          ((integrableOn_const (μ := volume) (s := Icc v w) (by simp [Real.volume_Icc])).add
            (hgint.const_mul Q)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hb t ht
    _ = (w - v) * P + Q * ∫ t in Icc v w, (1 + mfun t) ^ (-((d : ℝ) - 1)) := hRHS
    _ ≤ (w - v) * P + Q * c'⁻¹ := by
        have := mul_le_mul_of_nonneg_left hdecay hQ
        linarith

end WaveTurbulence.LadderDecay

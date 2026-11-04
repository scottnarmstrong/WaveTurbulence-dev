/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BadPairPhysicalSmall
public import WaveTurbulence.Foundations.Sumint.BilinearMinorPhysicalWindow
public import WaveTurbulence.Foundations.Sumint.BilinearParameterContinuity

/-!
# The complete case-(a) pair estimate in source times

The ordering strip is retained in the small region, giving a second
reciprocal scale. In the large region it is discarded while the full
Weyl reserve remains. Both contributions are uniform in continuous
outer-time spatial modulations, including the source affine ones.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint case (a), with its small- and large-region gains kept separate. -/
theorem exists_bilinear_physical_ordering_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ (a b : Mom d) (ξ ζ : ℝ → Mom d), Continuous ξ → Continuous ζ →
      ∀ c l u v w e : ℝ, 0 < c → l ≤ u → v ≤ w →
      (∀ t ∈ Icc v w, -(T₀*L^(2*γ)) ≤ c*(l-t) ∧ c*(u-t) ≤ T₀*L^(2*γ)) →
      (∫⁻ t in Icc v w, ∫⁻ s in Icc l u, if |t-e| ≤ |t-s| then
        ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) ≤
      ENNReal.ofReal (c⁻¹*(Cs*L^(2*d)/c) +
        (w-v)*c⁻¹*Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := exists_bilinear_physical_small_ordering_bound d hd
  obtain ⟨Cm,L₀,hCm,hL₀,hminor⟩ :=
    exists_bilinear_minor_physical_window_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL a b ξ ζ hξ hζ c l u v w e hc hlu hvw hwin
  have hL1 : 1 ≤ L := by linarith [hL₀.trans hL]
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let N := fun z : ℝ × ℝ =>
    ‖WeylSums.bilinearLatticeSum L (c*(z.1-z.2)) a b (ξ z.1) (ζ z.1)‖ₑ
  let A := fun z : ℝ × ℝ =>
    if |c*(z.2-z.1)| ≤ L ∧ |z.1-e| ≤ |z.1-z.2| then N z else 0
  let B := fun z : ℝ × ℝ =>
    if L ≤ |c*(z.2-z.1)| ∧ |c*(z.2-z.1)| ≤ T₀*L^(2*γ) then N z else 0
  have hN : Measurable N :=
    (continuous_bilinearLatticeSum_parameters hLp a b
      (fun z : ℝ × ℝ => c*(z.1-z.2)) (fun z => ξ z.1) (fun z => ζ z.1)
      (by fun_prop) (hξ.comp continuous_fst) (hζ.comp continuous_fst)).measurable.enorm
  have hA : Measurable A := by
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact measurableSet_le
          (continuous_abs.measurable.comp (measurable_const.mul (measurable_snd.sub measurable_fst)))
          measurable_const
      · exact measurableSet_le
          (continuous_abs.measurable.comp (measurable_fst.sub measurable_const))
          (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd))
    · exact hN
    · exact measurable_const
  have hAi : Measurable (fun t : ℝ => ∫⁻ s in Icc l u, A (t,s)) :=
    hA.lintegral_prod_right' (ν := volume.restrict (Icc l u))
  have hs : (∫⁻ t in Icc v w, ∫⁻ s in Icc l u, A (t,s)) ≤
      ENNReal.ofReal (c⁻¹*(Cs*L^(2*d)/c)) := by
    apply le_trans _ (hsmall hL1 hc a b ξ ζ e)
    calc
      _ ≤ ∫⁻ t in Icc v w, ∫⁻ s : ℝ, A (t,s) :=
        lintegral_mono (fun t => lintegral_mono' Measure.restrict_le_self le_rfl)
      _ ≤ ∫⁻ t : ℝ, ∫⁻ s : ℝ, A (t,s) := lintegral_mono' Measure.restrict_le_self le_rfl
  have hm : (∫⁻ t in Icc v w, ∫⁻ s in Icc l u, B (t,s)) ≤
      ENNReal.ofReal ((w-v)*c⁻¹*Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
    apply le_trans _ (hminor L hL a b ξ ζ c v w hc hvw)
    exact lintegral_mono (fun t => lintegral_mono' Measure.restrict_le_self le_rfl)
  calc
    _ ≤ ∫⁻ t in Icc v w, ∫⁻ s in Icc l u, A (t,s)+B (t,s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      change (if |t-e| ≤ |t-s| then N (t,s) else 0) ≤ A (t,s)+B (t,s)
      by_cases hstrip : |t-e| ≤ |t-s|
      · rw [ite_eq_left hstrip]
        by_cases hsm : |c*(s-t)| ≤ L
        · have hAe : A (t,s) = N (t,s) := by dsimp [A]; exact ite_eq_left ⟨hsm,hstrip⟩
          rw [hAe]
          exact le_add_right le_rfl
        · have hw : |c*(s-t)| ≤ T₀*L^(2*γ) := abs_le.mpr ⟨
            (hwin t ht).1.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.1 t) hc.le),
            (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 t) hc.le).trans (hwin t ht).2⟩
          have hBe : B (t,s) = N (t,s) := by dsimp [B]; exact ite_eq_left ⟨(lt_of_not_ge hsm).le,hw⟩
          rw [hBe]
          exact le_add_left le_rfl
      · rw [ite_eq_right hstrip]
        exact bot_le
    _ = (∫⁻ t in Icc v w, ∫⁻ s in Icc l u, A (t,s))+
        (∫⁻ t in Icc v w, ∫⁻ s in Icc l u, B (t,s)) := by
      have he (t : ℝ) : (∫⁻ s in Icc l u, A (t,s)+B (t,s)) =
          (∫⁻ s in Icc l u, A (t,s))+(∫⁻ s in Icc l u, B (t,s)) :=
        lintegral_add_left (hA.comp (measurable_const.prodMk measurable_id)) _
      simp_rw [he]
      exact lintegral_add_left hAi _
    _ ≤ _ := (add_le_add hs hm).trans_eq
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end WaveTurbulence.Sumint

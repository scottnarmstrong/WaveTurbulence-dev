/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Chain
public import WaveTurbulence.Foundations.Fourier.IntegralFourierL2

/-! # D1b-F FOLD 6: Plancherel interpolation (o82 Lemma 17.2)

* `eLpNorm_timeFourier_two`: Plancherel for the coordinate transform (main's `integral_fourier_eLpNorm_two`).
* `interp_le`: for `R ≥ 1`, `‖E‖_{𝔛^η} ≤ 2R^{1+η} ‖E‖₂ + R^{η-σ} ‖E‖_{𝔛^σ}` (Cauchy–Schwarz on
  `{⟨ξ⟩_max ≤ R} ⊂ [-R, R]²`, Plancherel; the strong norm outside).
* `interp_opt`: with `‖E‖₂ ≤ A c₂`, `‖E‖_{𝔛^{1/8}} ≤ e b` and `A > 0`:
  `‖E‖_{𝔛^η} ≤ (2c₂ + e) A^τ b^{1-τ}`, `τ = (1 - 8η)/9` (`R = (b/A)^{8/9}` if `b > A`; else the strong norm). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real FourierTransform

namespace WaveTurbulence.Flower.ProtOpsFold

/-- **Plancherel** for the coordinate time transform on `Fin 2 → ℝ`. -/
theorem eLpNorm_timeFourier_two {E : (Fin 2 → ℝ) → ℂ} (hEi : Integrable E) (hE2 : MemLp E 2) :
    eLpNorm (timeFourier E) 2 volume = eLpNorm E 2 volume := by
  set Ee : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => E (WithLp.ofLp x) with hEe
  have hEei : Integrable Ee :=
    (PiLp.volume_preserving_ofLp (Fin 2)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding |>.mpr hEi
  have hEe2 : MemLp Ee 2 := hE2.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 2))
  have hft : timeFourier E = (𝓕 Ee) ∘ (WithLp.toLp 2) := by
    funext ξ; exact timeFourier_eq_euclidean E ξ
  have hfc : 𝓕 Ee = timeFourier E ∘ WithLp.ofLp := by
    funext x
    simp only [Function.comp_apply, timeFourier_eq_euclidean E (WithLp.ofLp x), WithLp.toLp_ofLp, hEe]
  have hcont : Continuous (𝓕 Ee) := by
    rw [hfc]; exact (timeFourier_continuous hEi).comp (PiLp.continuous_ofLp 2 _)
  rw [hft, eLpNorm_comp_measurePreserving hcont.aestronglyMeasurable (PiLp.volume_preserving_toLp (Fin 2)),
    integral_fourier_eLpNorm_two hEei hEe2]
  exact eLpNorm_comp_measurePreserving hE2.aestronglyMeasurable (PiLp.volume_preserving_ofLp (Fin 2))

theorem volume_bracket_le {R : ℝ} (_hR : 0 ≤ R) :
    volume {ξ : Fin 2 → ℝ | timeBracket ξ ≤ R} ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (2 * R) := by
  have hsub : {ξ : Fin 2 → ℝ | timeBracket ξ ≤ R} ⊆ Icc (fun _ => -R) (fun _ => R) := by
    intro ξ hξ
    simp only [mem_ofPred_eq] at hξ
    have h : ∀ i, |ξ i| ≤ R := fun i =>
      (Real.abs_le_sqrt (by nlinarith : ξ i ^ 2 ≤ 1 + ξ i ^ 2)).trans
        ((bracket_le_timeBracket ξ i).trans hξ)
    exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩
  refine (measure_mono hsub).trans (le_of_eq ?_)
  simp only [Real.volume_Icc_pi, Fin.prod_univ_two, sub_neg_eq_add]
  congr 1 <;> ring_nf

/-- **The interpolation inequality.** -/
theorem interp_le {η σ R : ℝ} (hη : 0 ≤ η) (hησ : η ≤ σ) (hR : 1 ≤ R) {E : (Fin 2 → ℝ) → ℂ}
    (hEi : Integrable E) (hE2 : MemLp E 2) :
    timeFourierNorm η E ≤ ENNReal.ofReal (2 * R ^ (1 + η)) * eLpNorm E 2 volume +
      ENNReal.ofReal (R ^ (η - σ)) * timeFourierNorm σ E := by
  have hR0 : 0 < R := by linarith
  set S : Set (Fin 2 → ℝ) := {ξ | timeBracket ξ ≤ R} with hSdef
  have hS : MeasurableSet S := measurableSet_le (timeBracket_continuous 2).measurable measurable_const
  have hFc := timeFourier_continuous hEi
  rw [timeFourierNorm_eq_lintegral hEi, timeFourierNorm_eq_lintegral hEi,
    ← lintegral_add_compl (fun ξ => timeWeight η ξ * ‖timeFourier E ξ‖ₑ) hS]
  gcongr ?_ + ?_
  · -- low frequencies: Cauchy–Schwarz and Plancherel
    have hkey : ∫⁻ ξ in S, ‖timeFourier E ξ‖ₑ ≤ eLpNorm (timeFourier E) 2 volume * ENNReal.ofReal (2 * R) := by
      have hmS : AEStronglyMeasurable (timeFourier E) (volume.restrict S) := hFc.aestronglyMeasurable
      rw [← eLpNorm_one_eq_lintegral_enorm]
      swap
      · exact hmS
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hmS).trans ?_
      have hvol : (volume.restrict S) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≤
          ENNReal.ofReal (2 * R) := by
        rw [Measure.restrict_apply_univ]
        have he : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
        rw [he]
        calc volume S ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (2 * R) * ENNReal.ofReal (2 * R)) ^ (1 / 2 : ℝ) :=
              ENNReal.rpow_le_rpow (volume_bracket_le hR0.le) (by norm_num)
          _ = ENNReal.ofReal (2 * R) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_add_of_nonneg _ _
                (by norm_num) (by norm_num)]
              norm_num
      exact mul_le_mul' (eLpNorm_mono_measure (timeFourier E) Measure.restrict_le_self) hvol
    calc ∫⁻ ξ in S, timeWeight η ξ * ‖timeFourier E ξ‖ₑ
        ≤ ∫⁻ ξ in S, ENNReal.ofReal (R ^ η) * ‖timeFourier E ξ‖ₑ := by
          refine setLIntegral_mono' hS fun ξ hξ => ?_
          gcongr
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (timeBracket_pos ξ).le hξ hη)
      _ = ENNReal.ofReal (R ^ η) * ∫⁻ ξ in S, ‖timeFourier E ξ‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (R ^ η) * (eLpNorm (timeFourier E) 2 volume * ENNReal.ofReal (2 * R)) := by
          gcongr
      _ = ENNReal.ofReal (2 * R ^ (1 + η)) * eLpNorm E 2 volume := by
          rw [eLpNorm_timeFourier_two hEi hE2, mul_comm (eLpNorm E 2 volume), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [Real.rpow_add hR0, Real.rpow_one]; ring
  · -- high frequencies: the strong norm
    calc ∫⁻ ξ in Sᶜ, timeWeight η ξ * ‖timeFourier E ξ‖ₑ
        ≤ ∫⁻ ξ in Sᶜ, ENNReal.ofReal (R ^ (η - σ)) * (timeWeight σ ξ * ‖timeFourier E ξ‖ₑ) := by
          refine setLIntegral_mono' hS.compl fun ξ hξ => ?_
          rw [← mul_assoc]
          gcongr
          simp only [hSdef, mem_compl_iff, mem_ofPred_eq, not_le] at hξ
          unfold timeWeight
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have htb := timeBracket_pos ξ
          calc timeBracket ξ ^ η = timeBracket ξ ^ (η - σ) * timeBracket ξ ^ σ := by
                rw [← Real.rpow_add htb]; ring_nf
            _ ≤ R ^ (η - σ) * timeBracket ξ ^ σ :=
                mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hR0 hξ.le (by linarith))
                  (by positivity)
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (R ^ (η - σ)) * (timeWeight σ ξ * ‖timeFourier E ξ‖ₑ) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (R ^ (η - σ)) * ∫⁻ ξ, timeWeight σ ξ * ‖timeFourier E ξ‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The choice of `R`** (o82 Lemma 17.2). -/
theorem interp_opt {η : ℝ} (hη : 0 ≤ η) (hη8 : η < 1 / 8) {E : (Fin 2 → ℝ) → ℂ} (hEi : Integrable E)
    (hE2 : MemLp E 2) {A b c2 e : ℝ} (hA : 0 < A) (hb : 0 ≤ b) (hc2 : 0 ≤ c2) (he : 0 ≤ e)
    (hL2 : eLpNorm E 2 volume ≤ ENNReal.ofReal (A * c2))
    (hσ : timeFourierNorm (1 / 8) E ≤ ENNReal.ofReal (e * b)) :
    timeFourierNorm η E ≤
      ENNReal.ofReal ((2 * c2 + e) * (A ^ ((1 - 8 * η) / 9) * b ^ (1 - (1 - 8 * η) / 9))) := by
  set τ := (1 - 8 * η) / 9 with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτ1 : τ ≤ 1 := by rw [hτ]; linarith
  have hT0 : 0 ≤ A ^ τ * b ^ (1 - τ) := by positivity
  rcases le_or_gt b A with hbA | hbA
  · -- the strong norm suffices
    refine (timeFourierNorm_mono (by linarith) E).trans (hσ.trans (ENNReal.ofReal_le_ofReal ?_))
    have hbb : b ≤ A ^ τ * b ^ (1 - τ) := by
      calc b = b ^ τ * b ^ (1 - τ) := by
            rw [← Real.rpow_add' hb (by norm_num), add_sub_cancel, Real.rpow_one]
        _ ≤ A ^ τ * b ^ (1 - τ) := by
            gcongr
    nlinarith
  · -- `R = (b/A)^{8/9}`, written as `u^8` with `u = (b/A)^{1/9}`
    have hb0 : 0 < b := lt_trans hA hbA
    set u := (b / A) ^ ((1 : ℝ) / 9) with hu
    have hbA1 : 1 ≤ b / A := (one_le_div hA).mpr hbA.le
    have hu1 : 1 ≤ u := Real.one_le_rpow hbA1 (by norm_num)
    have hu0 : 0 < u := by linarith
    have hu9 : u ^ (9 : ℝ) = b / A := by
      rw [hu, ← Real.rpow_mul (by positivity)]; norm_num
    have hA' : A ≠ 0 := hA.ne'
    have hbu : b = A * u ^ (9 : ℝ) := by rw [hu9]; field_simp
    have hR1 : 1 ≤ u ^ (8 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
    have h := interp_le (σ := 1 / 8) hη (by linarith) hR1 hEi hE2
    refine h.trans ?_
    have hT : A ^ τ * b ^ (1 - τ) = A * u ^ (8 + 8 * η) := by
      rw [hbu, Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul hu0.le, ← mul_assoc,
        ← Real.rpow_add hA, show τ + (1 - τ) = 1 by ring, Real.rpow_one]
      congr 2; rw [hτ]; ring
    have e1 : (u ^ (8 : ℝ)) ^ (1 + η) = u ^ (8 + 8 * η) := by
      rw [← Real.rpow_mul hu0.le]; ring_nf
    have e2 : (u ^ (8 : ℝ)) ^ (η - 1 / 8) * u ^ (9 : ℝ) = u ^ (8 + 8 * η) := by
      rw [← Real.rpow_mul hu0.le, ← Real.rpow_add hu0]; ring_nf
    calc ENNReal.ofReal (2 * (u ^ (8 : ℝ)) ^ (1 + η)) * eLpNorm E 2 volume +
          ENNReal.ofReal ((u ^ (8 : ℝ)) ^ (η - 1 / 8)) * timeFourierNorm (1 / 8) E
        ≤ ENNReal.ofReal (2 * (u ^ (8 : ℝ)) ^ (1 + η)) * ENNReal.ofReal (A * c2) +
          ENNReal.ofReal ((u ^ (8 : ℝ)) ^ (η - 1 / 8)) * ENNReal.ofReal (e * b) := by gcongr
      _ = ENNReal.ofReal ((2 * c2 + e) * (A ^ τ * b ^ (1 - τ))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hT, e1]
          have e3 : (u ^ (8 : ℝ)) ^ (η - 1 / 8) * (e * b) = e * A * u ^ (8 + 8 * η) := by
            rw [hbu, ← e2]; ring
          rw [e3]; ring

end WaveTurbulence.Flower.ProtOpsFold

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.KinkAtom

/-! # PROT-PIN (D3-KINK): Fourier synthesis of the zero-extended terminal operator, one input

For `h` continuous with `h, ĥ ∈ L¹`: `h(x) = ∫ ĥ(l) e(l·x) dl` everywhere (`inversion2`), and for every `T`
(`inner_kink`, o73 (13.1)–(13.2) with the pin `s` above the clock):
`∫_{(s,T)} e^{πiA(u-s)} e(l₀T + l₁u) du = e(l₁s) e(l₀T) k_{A/2+l₁}(T - s)`, `k_z(v) = h_z(v₊)` (zero for `T ≤ s`).
With the output atom `oatom A s l T = e(l₁s) e(l₀T) Ψ₀(T - s) k_{A/2+l₁}(T - s)` and `Gsyn A s h = ∫ ĥ(l) oatom(l) dl`:
* `op_eq_synth`: on the window `|T - s| ≤ 1` the zero-extended operator equals `Gsyn` (everywhere, not a.e.);
* `oatom_norm_le`: `‖oatom l‖_{A^θ} ≤ 2^θ ⟨l⟩^θ Bk` (modulation by `l₀`, free translation, the kinked atom);
* `Gsyn_norm_le`: `‖Gsyn‖_{A^θ} ≤ 2^θ Bk ‖h‖_{A^θ}` (Minkowski in `l`);
* `enorm_Gsyn_le`, `lintegral_Gsyn_le`: the pointwise and `L¹` bounds used to sum over the countable family. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff FourierTransform

namespace WaveTurbulence.Flower.ProtPin

/-- Minkowski for the `A^θ` norm of a parameter integral (scalar case of main's `mixedFourierNorm00_integral_le`). -/
theorem timeFourierNorm_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ] {r : ℕ}
    (θ : ℝ) (F : α → (Fin r → ℝ) → ℂ) (hFm : Measurable (fun p : α × (Fin r → ℝ) => F p.1 p.2))
    (hFi : Integrable (fun p : α × (Fin r → ℝ) => F p.1 p.2) (μ.prod volume))
    (hFs : ∀ a, Integrable (F a)) :
    timeFourierNorm θ (fun t => ∫ a, F a t ∂μ) ≤ ∫⁻ a, timeFourierNorm θ (F a) ∂μ := by
  have h := Sumint.mixedFourierNorm00_integral_le (μ := μ) (V := Unit) θ (fun a t _ => F a t)
    (fun _ => hFm) (fun _ => hFi) (fun a _ => hFs a)
  rw [mixedFourierNorm00_unit] at h
  simpa only [mixedFourierNorm00_unit] using h

/-- The `L¹` mass of the transform is at most the `A^θ` norm, `θ ≥ 0`. -/
theorem lintegral_enorm_le_norm {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {f : (Fin r → ℝ) → ℂ} (hf : Integrable f) :
    ∫⁻ ξ, ‖timeFourier f ξ‖ₑ ≤ timeFourierNorm θ f := by
  rw [timeFourierNorm_eq_lintegral hf]
  refine lintegral_mono fun ξ => ?_
  have hw : (1 : ℝ≥0∞) ≤ timeWeight θ ξ := by
    simpa only [timeWeight, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)
  calc ‖timeFourier f ξ‖ₑ = 1 * ‖timeFourier f ξ‖ₑ := (one_mul _).symm
    _ ≤ timeWeight θ ξ * ‖timeFourier f ξ‖ₑ := by gcongr

theorem tp_apply (r : ℕ) (t ξ : Fin r → ℝ) : timePairing r t ξ = ∑ i, t i * ξ i := rfl

theorem katom_joint : Continuous (fun p : ℝ × ℝ => katom p.1 p.2) :=
  (Psi0_continuous.comp continuous_snd).mul kink_continuous

theorem norm_katom_le_two (z v : ℝ) : ‖katom z v‖ ≤ 2 := by
  by_cases hv : |v| < 2
  · refine (norm_katom_le z v).trans ?_
    have := norm_Psi0_le v
    nlinarith [norm_nonneg (Psi0 v), abs_nonneg v]
  · rw [katom, Psi0_zero (not_lt.mp hv), zero_mul, norm_zero]
    norm_num

/-- The output atom of the input frequency `l = (l₀, l₁)`: `e(l₁s) e(l₀T) Ψ₀(T - s) k_{A/2+l₁}(T - s)`. -/
def oatom (A s : ℝ) (l : Fin 2 → ℝ) (T : Fin 1 → ℝ) : ℂ :=
  (Real.fourierChar (l 1 * s) : ℂ) •
    (Real.fourierChar (timePairing 1 T (fun _ => l 0)) • katom (A / 2 + l 1) ((T + (fun _ => -s : Fin 1 → ℝ)) 0))

theorem oatom_apply (A s : ℝ) (l : Fin 2 → ℝ) (T : Fin 1 → ℝ) :
    oatom A s l T = Complex.exp (((2 * Real.pi * (l 1 * s) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((2 * Real.pi * (T 0 * l 0) : ℝ) : ℂ) * Complex.I) * katom (A / 2 + l 1) (T 0 - s) := by
  have hp : timePairing 1 T (fun _ => l 0) = T 0 * l 0 := by
    simp [tp_apply]
  simp only [oatom, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, hp, Pi.add_apply,
    ← sub_eq_add_neg]
  ring

theorem oatom_continuous (A s : ℝ) :
    Continuous (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => oatom A s p.1 p.2) := by
  simp only [oatom_apply]
  have hk : Continuous (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => katom (A / 2 + p.1 1) (p.2 0 - s)) :=
    katom_joint.comp (f := fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => (A / 2 + p.1 1, p.2 0 - s)) (by fun_prop)
  have he : Continuous (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) =>
      Complex.exp (((2 * Real.pi * (p.1 1 * s) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (p.2 0 * p.1 0) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  exact he.mul hk

/-- `m_s(T) = |Ψ₀(T - s)| |T - s|`, an integrable majorant of every output atom. -/
def mk (s : ℝ) (T : Fin 1 → ℝ) : ℝ := ‖Psi0 (T 0 - s)‖ * |T 0 - s|

theorem mk_continuous (s : ℝ) : Continuous (mk s) := by
  unfold mk
  have h1 : Continuous (fun T : Fin 1 → ℝ => T 0 - s) := by fun_prop
  exact (Psi0_continuous.comp h1).norm.mul (continuous_abs.comp h1)

theorem mk_integrable (s : ℝ) : Integrable (mk s) := by
  have hm : Integrable (fun v : ℝ => ‖Psi0 v‖ * |v|) :=
    (Psi0_continuous.norm.mul continuous_abs).integrable_of_hasCompactSupport
      (Psi0_compact.norm.mul_right)
  exact (volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_of_integrable (hm.comp_sub_right s)

theorem norm_oatom_le (A s : ℝ) (l : Fin 2 → ℝ) (T : Fin 1 → ℝ) : ‖oatom A s l T‖ ≤ mk s T := by
  rw [oatom_apply, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    one_mul, one_mul]
  exact norm_katom_le _ _

theorem norm_oatom_le_two (A s : ℝ) (l : Fin 2 → ℝ) (T : Fin 1 → ℝ) : ‖oatom A s l T‖ ≤ 2 := by
  rw [oatom_apply, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    one_mul, one_mul]
  exact norm_katom_le_two _ _

theorem oatom_integrable (A s : ℝ) (l : Fin 2 → ℝ) : Integrable (oatom A s l) :=
  (mk_integrable s).mono'
    ((oatom_continuous A s).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (norm_oatom_le A s l))

theorem timeWeight_const_le {θ : ℝ} (hθ : 0 ≤ θ) (l : Fin 2 → ℝ) :
    timeWeight θ (fun _ : Fin 1 => l 0) ≤ timeWeight θ l := by
  unfold timeWeight
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (timeBracket_pos _).le _ hθ
  rw [Sumint.timeBracket_one_eq]
  exact bracket_le_timeBracket l 0

/-- The norm of an output atom: `‖oatom l‖_{A^θ} ≤ 2^θ ⟨l⟩^θ Bk`. -/
theorem oatom_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (A s : ℝ) (l : Fin 2 → ℝ) :
    timeFourierNorm θ (oatom A s l) ≤ ENNReal.ofReal (2 ^ θ) * timeWeight θ l * ENNReal.ofReal Bk := by
  have e : oatom A s l = fun T => (Real.fourierChar (l 1 * s) : ℂ) •
      (Real.fourierChar (timePairing 1 T (fun _ => l 0)) •
        (fun T' : Fin 1 → ℝ => katom (A / 2 + l 1) (T' 0)) (T + (fun _ => -s : Fin 1 → ℝ))) := rfl
  rw [e, timeFourierNorm_smul]
  have h1 : ‖(Real.fourierChar (l 1 * s) : ℂ)‖ₑ = 1 := by
    rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  rw [h1, one_mul]
  refine (timeFourierNorm_modulate_le hθ0 _ _).trans ?_
  have ht := timeFourierNorm_translate θ (fun T' : Fin 1 → ℝ => katom (A / 2 + l 1) (T' 0))
    (fun _ => -s : Fin 1 → ℝ)
  rw [ht]
  gcongr
  · exact timeWeight_const_le hθ0 l
  · exact katom_norm_le hθ1 _

/-- The inner identity (o73 (13.1)–(13.2), pin `s` above the clock): the zero extension below `s` is the kink. -/
theorem inner_kink (A s : ℝ) (l : Fin 2 → ℝ) (T : ℝ) :
    ∫ u in Set.Ioo s T, Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * timePairing 2 l ![T, u] : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (l 1 * s) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (T * l 0) : ℝ) : ℂ) * Complex.I) * kink (A / 2 + l 1) (T - s) := by
  rcases le_or_gt T s with hT | hT
  · rw [Set.Ioo_eq_empty (not_lt.mpr hT), Measure.restrict_empty, integral_zero_measure,
      kink_of_nonpos _ (by linarith), mul_zero]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le]
    have hsub := intervalIntegral.integral_comp_add_left (a := 0) (b := T - s)
      (fun u : ℝ => Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * timePairing 2 l ![T, u] : ℝ) : ℂ) * Complex.I)) s
    simp only [add_zero, add_sub_cancel] at hsub
    rw [← hsub, kink, max_eq_left (by linarith : (0:ℝ) ≤ T - s)]
    unfold ProtTa.hz
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun w _ => ?_)
    simp only [tp_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Fourier inversion at every point for a continuous `h` with `h, ĥ ∈ L¹`. -/
theorem inversion2 {h : (Fin 2 → ℝ) → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hhat : Integrable (timeFourier h)) (x : Fin 2 → ℝ) :
    h x = ∫ l, Complex.exp (((2 * Real.pi * timePairing 2 l x : ℝ) : ℂ) * Complex.I) * timeFourier h l := by
  conv_lhs => rw [← timeFourier_inversion hi hhat hc x]
  change (∫ l, Real.fourierChar (-timePairing 2 l (-x)) • timeFourier h l) = _
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  simp only [map_neg, neg_neg, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]

/-- The synthesized output of one input. -/
def Gsyn (A s : ℝ) (h : (Fin 2 → ℝ) → ℂ) (T : Fin 1 → ℝ) : ℂ :=
  ∫ l, timeFourier h l * oatom A s l T

/-- On the window `|T - s| ≤ 1` the zero-extended terminal operator equals the synthesized output. -/
theorem op_eq_synth (A s : ℝ) {h : (Fin 2 → ℝ) → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hhat : Integrable (timeFourier h)) (T : Fin 1 → ℝ) (hT : |T 0 - s| ≤ 1) :
    ∫ u in Set.Ioo s (T 0), Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) * h ![T 0, u] =
      Gsyn A s h T := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioo s (T 0))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hhc : Continuous (timeFourier h) := timeFourier_continuous hi
  have step1 : ∫ u in Set.Ioo s (T 0), Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        h ![T 0, u] =
      ∫ u in Set.Ioo s (T 0), ∫ l, Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((2 * Real.pi * timePairing 2 l ![T 0, u] : ℝ) : ℂ) * Complex.I) *
          timeFourier h l) := by
    congr 1
    funext u
    rw [inversion2 hc hi hhat ![T 0, u], ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (u : ℝ) (l : Fin 2 → ℝ) =>
      Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((2 * Real.pi * timePairing 2 l ![T 0, u] : ℝ) : ℂ) * Complex.I) * timeFourier h l))
      ((volume.restrict (Set.Ioo s (T 0))).prod volume) := by
    have h1 : Integrable (fun p : ℝ × (Fin 2 → ℝ) => (1 : ℝ) * ‖timeFourier h p.2‖)
        ((volume.restrict (Set.Ioo s (T 0))).prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun l => ‖timeFourier h l‖)
        (integrable_const _) hhat.norm
    refine h1.mono' ?_ (ae_of_all _ fun p => ?_)
    · have : Continuous (Function.uncurry fun (u : ℝ) (l : Fin 2 → ℝ) =>
          Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((2 * Real.pi * timePairing 2 l ![T 0, u] : ℝ) : ℂ) * Complex.I) *
              timeFourier h l)) := by
        simp only [tp_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  rw [step1, integral_integral_swap hint]
  unfold Gsyn
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  dsimp only
  have h2 : ∫ u in Set.Ioo s (T 0), Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((2 * Real.pi * timePairing 2 l ![T 0, u] : ℝ) : ℂ) * Complex.I) * timeFourier h l) =
      (∫ u in Set.Ioo s (T 0), Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * timePairing 2 l ![T 0, u] : ℝ) : ℂ) * Complex.I)) * timeFourier h l := by
    rw [← integral_mul_const]
    congr 1
    funext u
    ring
  rw [h2, inner_kink, oatom_apply, katom, Psi0_one hT, one_mul]
  ring

theorem Gsyn_prod_integrable (A s : ℝ) {h : (Fin 2 → ℝ) → ℂ} (hhat : Integrable (timeFourier h))
    (hhc : Continuous (timeFourier h)) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => timeFourier h p.1 * oatom A s p.1 p.2)
      (volume.prod volume) := by
  have h1 : Integrable (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => ‖timeFourier h p.1‖ * mk s p.2)
      (volume.prod volume) :=
    Integrable.mul_prod (f := fun l => ‖timeFourier h l‖) (g := mk s) hhat.norm (mk_integrable s)
  refine h1.mono' ((hhc.comp continuous_fst).mul (oatom_continuous A s)).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_oatom_le A s p.1 p.2) (norm_nonneg _)

theorem Gsyn_integrable (A s : ℝ) {h : (Fin 2 → ℝ) → ℂ} (hhat : Integrable (timeFourier h))
    (hhc : Continuous (timeFourier h)) : Integrable (Gsyn A s h) :=
  (Gsyn_prod_integrable A s hhat hhc).integral_prod_right

theorem Gsyn_measurable (A s : ℝ) {h : (Fin 2 → ℝ) → ℂ} (hhc : Continuous (timeFourier h)) :
    Measurable (Gsyn A s h) := by
  have hc : Continuous (Function.uncurry fun (T : Fin 1 → ℝ) (l : Fin 2 → ℝ) =>
      timeFourier h l * oatom A s l T) :=
    (hhc.comp continuous_snd).mul ((oatom_continuous A s).comp continuous_swap)
  exact (StronglyMeasurable.integral_prod_right (ν := volume) hc.stronglyMeasurable).measurable

theorem enorm_Gsyn_le (A s : ℝ) (h : (Fin 2 → ℝ) → ℂ) (T : Fin 1 → ℝ) :
    ‖Gsyn A s h T‖ₑ ≤ 2 * ∫⁻ l, ‖timeFourier h l‖ₑ := by
  unfold Gsyn
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ l, ‖timeFourier h l * oatom A s l T‖ₑ ≤ ∫⁻ l, 2 * ‖timeFourier h l‖ₑ := by
        refine lintegral_mono fun l => ?_
        rw [enorm_mul, mul_comm]
        gcongr
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖oatom A s l T‖ ≤ ENNReal.ofReal 2 :=
              ENNReal.ofReal_le_ofReal (norm_oatom_le_two A s l T)
          _ = 2 := by norm_num
    _ = 2 * ∫⁻ l, ‖timeFourier h l‖ₑ := lintegral_const_mul' _ _ (by norm_num)

theorem lintegral_Gsyn_le (A s : ℝ) (h : (Fin 2 → ℝ) → ℂ) :
    ∫⁻ T, ‖Gsyn A s h T‖ₑ ≤ (∫⁻ l, ‖timeFourier h l‖ₑ) * ∫⁻ T, ENNReal.ofReal (mk s T) := by
  calc ∫⁻ T, ‖Gsyn A s h T‖ₑ ≤ ∫⁻ T, (∫⁻ l, ‖timeFourier h l‖ₑ) * ENNReal.ofReal (mk s T) := by
        refine lintegral_mono fun T => ?_
        unfold Gsyn
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun l => ?_
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_oatom_le A s l T)
    _ = _ := lintegral_const_mul _ (mk_continuous s).measurable.ennreal_ofReal

/-- Minkowski in `l`: `‖Gsyn A s h‖_{A^θ} ≤ 2^θ Bk ‖h‖_{A^θ}`. -/
theorem Gsyn_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (A s : ℝ) {h : (Fin 2 → ℝ) → ℂ}
    (hfin : timeFourierNorm θ h < ⊤) :
    timeFourierNorm θ (Gsyn A s h) ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal Bk * timeFourierNorm θ h := by
  have hi := integrable_of_timeFourierNorm_lt_top hfin
  have hhat := integrable_timeFourier_of_norm_lt_top hθ0 hfin
  have hhc := timeFourier_continuous hi
  have hm : Measurable (fun p : (Fin 2 → ℝ) × (Fin 1 → ℝ) => timeFourier h p.1 * oatom A s p.1 p.2) :=
    ((hhc.comp continuous_fst).mul (oatom_continuous A s)).measurable
  have hslice : ∀ l, Integrable (fun T => timeFourier h l * oatom A s l T) :=
    fun l => (oatom_integrable A s l).const_mul _
  have hM := timeFourierNorm_integral_le (μ := volume) θ (fun l T => timeFourier h l * oatom A s l T) hm
    (Gsyn_prod_integrable A s hhat hhc) hslice
  refine hM.trans ?_
  rw [timeFourierNorm_eq_lintegral hi]
  calc ∫⁻ l, timeFourierNorm θ (fun T => timeFourier h l * oatom A s l T)
      ≤ ∫⁻ l, (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal Bk) * (timeWeight θ l * ‖timeFourier h l‖ₑ) := by
        refine lintegral_mono fun l => ?_
        have e : (fun T => timeFourier h l * oatom A s l T) = fun T => timeFourier h l • oatom A s l T :=
          rfl
        rw [e, timeFourierNorm_smul]
        calc ‖timeFourier h l‖ₑ * timeFourierNorm θ (oatom A s l)
            ≤ ‖timeFourier h l‖ₑ * (ENNReal.ofReal (2 ^ θ) * timeWeight θ l * ENNReal.ofReal Bk) := by
              gcongr
              exact oatom_norm_le hθ0 hθ1 A s l
          _ = _ := by ring
    _ = _ := lintegral_const_mul _ ((timeWeight_measurable θ).mul hhc.measurable.enorm)

end WaveTurbulence.Flower.ProtPin

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Slots

/-! # PROT-OPS slots: `FixedIntervalBound` (o104 Lemma 7.1 (5))

The output integrates the last slot over a unit interval; null-set changes of the input move it only on a null set
of the output variables (Fubini), so the extension is a piecewise one. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsSlot

open WaveTurbulence.Flower.ProtOps

theorem ae_snoc {r : ℕ} {f g : (Fin (r + 1) → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ y : Fin r → ℝ, ∀ᵐ u : ℝ, f (Fin.snoc y u) = g (Fin.snoc y u) := by
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)
  have h1 := hmp.symm.quasiMeasurePreserving.ae h
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin r → ℝ))) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae
    (p := fun z : ℝ × (Fin r → ℝ) => f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm z) =
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm z)) (by
    rw [← Measure.volume_eq_prod]; exact h1)
  have h3 := Measure.ae_ae_of_ae_prod h2
  refine h3.mono fun y hy => hy.mono fun u hu => ?_
  have e : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).symm (u, y) = Fin.snoc y u := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact Fin.insertNth_last' u y
  rw [Prod.swap_prod_mk] at hu
  simpa only [e] using hu

/-- The interval multiplier `c_A(s) = ∫_{q'}^{q'+1} e^{πiAu} e(us) du`. -/
def cI (A q' s : ℝ) : ℂ :=
  ∫ u in q'..q' + 1, Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * (Real.fourierChar (u * s) : ℂ)

theorem norm_cI_le (A q' s : ℝ) : ‖cI A q' s‖ ≤ 1 := by
  unfold cI
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := q') (b := q' + 1)
    (f := fun u : ℝ => Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * (Real.fourierChar (u * s) : ℂ))
    (C := 1) (fun u _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Circle.norm_coe, one_mul])
  simpa using this

theorem cI_continuous (A q' : ℝ) : Continuous (cI A q') := by
  unfold cI
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun s u : ℝ =>
    Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * (Real.fourierChar (u * s) : ℂ)) ?_ q' (q' + 1)
  refine Continuous.mul (by fun_prop) ?_
  exact cont_fourierChar_coe (by fun_prop)

theorem rep_formula {r : ℕ} (f : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) :
    timeFourier (timeFourier f) (-t) =
      ∫ l, timeFourier f l * (Real.fourierChar (timePairing r t l) : ℂ) := by
  change (∫ ξ, Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ) = _
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  have h1 : timePairing r l t = timePairing r t l := by simp [timePairing, dotProduct_comm]
  simp only [Circle.smul_def, smul_eq_mul, map_neg, neg_neg, h1]
  ring

theorem interval_trace_ae {θ : ℝ} (hθ0 : 0 ≤ θ) {r : ℕ} (A q' : ℝ) {V : Type*}
    {H : (Fin (r + 1) → ℝ) → V → ℂ} (hH : mixedFourierNorm00 θ H < ⊤) (k : V) :
    ∀ᵐ y : Fin r → ℝ,
      (∫ u in q'..q' + 1, Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * H (Fin.snoc y u) k) =
        ∫ l, timeFourier (fun t => H t k) l *
          (cI A q' (l (Fin.last r)) * (Real.fourierChar (timePairing r y (Fin.init l)) : ℂ)) := by
  have hk : Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH k
  have hhat : Integrable (timeFourier fun t => H t k) :=
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  have hae := Regref.timeFourier_inversion_ae hk hhat
  filter_upwards [ae_snoc hae.symm] with y hy
  set f : (Fin (r + 1) → ℝ) → ℂ := fun t => H t k with hf
  set fh := timeFourier f with hfh
  set E : ℝ → ℂ := fun u => Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) with hE
  set P : (Fin (r + 1) → ℝ) → ℂ := fun l => (Real.fourierChar (timePairing r y (Fin.init l)) : ℂ) with hP
  have hEn : ∀ u, ‖E u‖ = 1 := fun u => Complex.norm_exp_ofReal_mul_I _
  have step1 : (∫ u in q'..q' + 1, E u * f (Fin.snoc y u)) =
      ∫ u in q'..q' + 1, E u * ∫ l, fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (hy.mono fun u hu _ => ?_)
    have hu' : f (Fin.snoc y u) = timeFourier (timeFourier f) (-Fin.snoc y u) := hu
    rw [hu', rep_formula]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    beta_reduce
    rw [timePairing_snoc, fourierChar_coe_add]
  show _ = ∫ l, fh l * (cI A q' (l (Fin.last r)) * P l)
  refine step1.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hcontP : Continuous P := by
    refine cont_fourierChar_coe ?_
    exact (LinearMap.continuous_of_finiteDimensional (timePairing r y)).comp
      (continuous_pi fun i => continuous_apply _)
  have hcF : Continuous fh := timeFourier_continuous hk
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hint : Integrable (Function.uncurry fun (u : ℝ) (l : Fin (r + 1) → ℝ) =>
      E u * (fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ))))
      ((volume.restrict (Set.Ioc q' (q' + 1))).prod volume) := by
    have h1 : Integrable (fun z : ℝ × (Fin (r + 1) → ℝ) => (1 : ℝ) * ‖fh z.2‖)
        ((volume.restrict (Set.Ioc q' (q' + 1))).prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun l => ‖fh l‖)
        (integrable_const _) hhat.norm
    refine h1.mono' ?_ (ae_of_all _ fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have : Continuous fun z : ℝ × (Fin (r + 1) → ℝ) =>
          ((Real.fourierChar (z.1 * z.2 (Fin.last r)) : Circle) : ℂ) :=
        cont_fourierChar_coe (continuous_fst.mul ((continuous_apply _).comp continuous_snd))
      exact (hEc.comp continuous_fst).mul ((hcF.comp continuous_snd).mul
        ((hcontP.comp continuous_snd).mul this))
    · simp only [Function.uncurry, norm_mul, hEn, Circle.norm_coe, one_mul, mul_one]
      simp [hP]
  have hsw := integral_integral_swap (f := fun (u : ℝ) (l : Fin (r + 1) → ℝ) =>
      E u * (fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ)))) hint
  simp_rw [← integral_const_mul]
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  beta_reduce
  unfold cI
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [hE]; ring

theorem fixedIntervalBound : ProtDefs.FixedIntervalBound := by
  intro d r θ hθ
  obtain ⟨C, hC0, hC⟩ := xnormRestr_le_of_ext (d := d) hθ (r + 1) r
  refine ⟨C, hC0, fun A q q' G K => ?_⟩
  have hν : Continuous (Fin.init : (Fin (r + 1) → ℝ) → Fin r → ℝ) :=
    continuous_pi fun i => continuous_apply _
  have hc : Continuous fun l : Fin (r + 1) → ℝ => cI A q' (l (Fin.last r)) :=
    (cI_continuous A q').comp (continuous_apply _)
  classical
  refine hC q _ (fun y hy i => by simpa using hy i (Set.mem_univ i)) K _ G Fin.init hν
    timeBracket_init_le (fun l => cI A q' (l (Fin.last r))) hc (fun l => norm_cI_le _ _ _) ?_
  intro hG
  refine ⟨fun y k => if y ∈ (Set.pi Set.univ fun _ : Fin r => Set.Icc q (q + 1)) then
      ∫ u in q'..q' + 1, Complex.exp (((Real.pi * A * u : ℝ) : ℂ) * Complex.I) * G (Fin.snoc y u) k
    else synth (linAtom (cutK r q) Fin.init (fun l : Fin (r + 1) → ℝ => cI A q' (l (Fin.last r)))) G y k,
    fun y hy k _ => by beta_reduce; rw [if_pos hy], fun k => ?_⟩
  filter_upwards [interval_trace_ae hθ A q' hG k] with y hy
  by_cases hyB : y ∈ (Set.pi Set.univ fun _ : Fin r => Set.Icc q (q + 1))
  · rw [if_pos hyB]
    rw [hy]
    unfold synth
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    beta_reduce
    simp only [linAtom, Circle.smul_def, smul_eq_mul]
    rw [cutK_one (fun i => by simpa using hyB i (Set.mem_univ i))]
    ring
  · rw [if_neg hyB]

end WaveTurbulence.Flower.ProtOpsSlot

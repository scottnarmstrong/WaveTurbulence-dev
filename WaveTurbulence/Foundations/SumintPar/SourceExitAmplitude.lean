/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BoxEndpointRepresentation
public import WaveTurbulence.Foundations.SumintPar.LocalPhaseExtension

/-!
# The selected source endpoint amplitudes and their exact characters

Each coordinate endpoint contributes a bounded real damping factor and
a Fourier character involving only that coordinate and the distinguished
first input time. Averaging weights and the interval-order indicator
preserve measurability and input integrability, with norm at most the
original input coefficient on its actual local domain.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Real exponential damping at one literal selected source endpoint. -/
@[expose] noncomputable def sourceExitDamping {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) : ℝ :=
  Real.exp (u v+2*u (firstTime D hI)-((D.q v:ℝ)+(if upper then 1 else 0)))

/-- The source endpoint amplitude after removing all frequency characters. -/
@[expose] noncomputable def sourceExitAmplitude {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (u : D.S.TVar → ℝ) : ℂ :=
  if lowerTimeExit D hI u ≤ upperTimeExit D hI u then
    ((timeExitWeight D hI upper v u*sourceExitDamping D hI upper v u:ℝ):ℂ)*F u else 0

/-- Endpoint exponential factors contain only one selected coordinate and the distinguished first time. -/
theorem boxEndpointTerm_eq_characters (Q v w : ℝ) (ξ : Fin 3 → ℝ) :
    boxEndpointTerm (Q-v) w ξ = (Real.exp (v+2*w-Q):ℂ)*
      (Real.fourierChar (-ξ 0*Q):ℂ)*(Real.fourierChar (ξ 0*v-(ξ 1+ξ 2)*w):ℂ) := by
  unfold boxEndpointTerm
  simp_rw [Real.fourierChar_apply,Complex.ofReal_exp]
  repeat rw [← Complex.exp_add]
  congr 1
  unfold exponentialRate
  push_cast
  ring

/-- The exact coordinate endpoint character formula in the source variables. -/
theorem source_boxEndpointTerm_eq_characters {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) (ξ : Fin 3 → ℝ) :
    boxEndpointTerm (timeExitCoordinate D upper v u) (u (firstTime D hI)) ξ =
      (sourceExitDamping D hI upper v u:ℂ)*
        (Real.fourierChar (-ξ 0*((D.q v:ℝ)+(if upper then 1 else 0))):ℂ)*
        (Real.fourierChar (ξ 0*u v-(ξ 1+ξ 2)*u (firstTime D hI)):ℂ) :=
  boxEndpointTerm_eq_characters _ _ _ _

/-- The damping factor is continuous in the full input-time vector. -/
theorem continuous_sourceExitDamping {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) : Continuous (sourceExitDamping D hI upper v) := by
  unfold sourceExitDamping
  fun_prop

/-- The actual static negative input times make each damping factor lie in the unit interval. -/
theorem sourceExitDamping_mem_Icc {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) (hu : ∀ w, u w ≤ 0) :
    sourceExitDamping D hI upper v u ∈ Icc (0:ℝ) 1 := by
  refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
  have hq : 0 ≤ (D.q v:ℝ) := Nat.cast_nonneg _
  have he : (0:ℝ) ≤ (if upper then 1 else 0) := by cases upper <;> norm_num
  linarith only [hu v,hu (firstTime D hI),hq,he]

/-- A measurable input coefficient gives measurable selected endpoint amplitudes. -/
theorem measurable_sourceExitAmplitude {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F) :
    Measurable (sourceExitAmplitude D hI upper v F) := by
  have hm := ((measurable_timeExitWeight D hI upper v).mul
    (continuous_sourceExitDamping D hI upper v).measurable).complex_ofReal
  exact Measurable.ite (measurableSet_le (continuous_lowerTimeExit D hI).measurable
    (continuous_upperTimeExit D hI).measurable) (hm.mul hF) measurable_const

/-- Every selected source endpoint amplitude has norm at most that of its input coefficient. -/
theorem norm_sourceExitAmplitude_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (u : D.S.TVar → ℝ)
    (hu : ∀ w, u w ≤ 0) : ‖sourceExitAmplitude D hI upper v F u‖ ≤ ‖F u‖ := by
  have hw := timeExitWeight_mem_Icc D hI upper v u
  have hd := sourceExitDamping_mem_Icc D hI upper v u hu
  unfold sourceExitAmplitude
  split_ifs
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw.1 hd.1)]
    have hh : timeExitWeight D hI upper v u*sourceExitDamping D hI upper v u ≤ 1 :=
      (mul_le_mul hw.2 hd.2 hd.1 zero_le_one).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · exact (norm_zero).le.trans (norm_nonneg _)

/-- Selected amplitudes retain genuine native input-time integrability. -/
theorem integrableOn_sourceExitAmplitude {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (hFm : Measurable F)
    (c h : ℝ) (hFi : IntegrableOn F (localInputTimeDomain D c h)) :
    IntegrableOn (sourceExitAmplitude D hI upper v F) (localInputTimeDomain D c h) := by
  apply hFi.norm.mono' (measurable_sourceExitAmplitude D hI upper v F hFm).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem (measurableSet_localInputTimeDomain D c h)] with u hu
  exact norm_sourceExitAmplitude_le D hI upper v F u (fun w => (hu.2.1 w).le)

end WaveTurbulence.SumintPar

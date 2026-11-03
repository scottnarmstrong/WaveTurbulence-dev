/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TimeForest

/-!
# Absolute-volume control of time-forest integrals

These are nonoscillatory estimates and integrability facts for the actual
heap domain. They are separate from the resonance-decay theorem.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis.TimeForest

variable {n : ℕ}

theorem measurableSet_timeDomain (T : TimeForest n) (t : ℝ) (σ : Fin n → ℝ) :
    MeasurableSet (T.timeDomain t σ) := by
  have hb : MeasurableSet {s : Fin n → ℝ | ∀ v, s v ∈ Icc 0 t} := by
    have heq : {s : Fin n → ℝ | ∀ v, s v ∈ Icc 0 t} = Set.pi univ (fun _ => Icc 0 t) := by
      ext s
      simp only [mem_ofPred_eq, mem_pi, mem_univ, forall_const]
    rw [heq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have he : MeasurableSet {s : Fin n → ℝ | ∀ v,
      match T.parent v with
      | none => s v + σ v < t
      | some p => s v + σ v < s p} := by
    have haux (v : Fin n) : MeasurableSet {s : Fin n → ℝ |
        match T.parent v with
        | none => s v + σ v < t
        | some p => s v + σ v < s p} := by
      cases h : T.parent v with
      | none => exact measurableSet_lt ((measurable_pi_apply v).add measurable_const) measurable_const
      | some p => exact measurableSet_lt ((measurable_pi_apply v).add measurable_const) (measurable_pi_apply p)
    convert MeasurableSet.iInter haux using 1
    ext s
    simp only [mem_ofPred_eq, mem_iInter]
  exact hb.inter he

theorem timeDomain_subset_heapOrderRegion (T : TimeForest n) (t : ℝ) {σ : Fin n → ℝ}
    (hσ : ∀ v, 0 ≤ σ v) :
    T.timeDomain t σ ⊆ heapOrderRegion (fun p v => T.parent v = some p) t := by
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro p v hpar
  have hh := hs.2 v
  rw [hpar] at hh
  linarith only [hh, hσ v]

/-- Absolute values of all phase factors equal one. -/
theorem norm_integrand (α s : Fin n → ℝ) :
    ‖∏ v, Complex.exp ((Real.pi * α v * s v : ℝ) * Complex.I)‖ = 1 := by
  rw [norm_prod]
  simp only [Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one]

/-- The absolute-volume estimate. It does not claim resonance decay. -/
theorem enorm_integral_le_heapVolume (T : TimeForest n) {t : ℝ} (ht : 0 ≤ t)
    {σ : Fin n → ℝ} (hσ : ∀ v, 0 ≤ σ v) (α : Fin n → ℝ) :
    ‖T.integral t σ α‖ₑ ≤
      (linearExtensions (fun p v => T.parent v = some p)).card *
        ENNReal.ofReal (t ^ n / (Nat.factorial n : ℝ)) := by
  calc
    ‖T.integral t σ α‖ₑ ≤ ∫⁻ s in T.timeDomain t σ,
        ‖∏ v, Complex.exp ((Real.pi * α v * s v : ℝ) * Complex.I)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = volume (T.timeDomain t σ) := by
      simp_rw [← ofReal_norm, norm_integrand, ENNReal.ofReal_one]
      rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
    _ ≤ volume (heapOrderRegion (fun p v => T.parent v = some p) t) :=
      measure_mono (T.timeDomain_subset_heapOrderRegion t hσ)
    _ = _ := volume_heapOrderRegion _ ht

end WaveTurbulence.Analysis.TimeForest

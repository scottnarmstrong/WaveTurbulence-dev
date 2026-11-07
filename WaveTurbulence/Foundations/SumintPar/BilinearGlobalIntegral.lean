/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearSmallIntegral
public import WaveTurbulence.Foundations.SumintPar.IntegralCover
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum2
import Mathlib.Tactic

/-!
# The complete bilinear time-window estimate

Combining the exact Poisson small region and the landed Weyl large
region gives a uniform `C L^(2d)` integral before rescaling time.
Rescaling by `δ L^(2γ)` yields the source pair factor
`C δ^{-1} L^{2(d-γ)}`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Closed symmetric time windows are exactly absolute-value windows. -/
theorem abs_window_eq_Icc (B : ℝ) : {s : ℝ | |s| ≤ B} = Icc (-B) B := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]

/-- The full source bilinear window, including its absolute integrability. -/
theorem exists_bilinear_global_integral_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2 * ((d : ℝ)-1) * (1-γ)) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 2 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d,
      IntegrableOn (fun s => ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖)
        {s : ℝ | |s| ≤ T₀ * L^(2*γ)} ∧
      (∫ s in {s : ℝ | |s| ≤ T₀ * L^(2*γ)},
        ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) ≤ C * L^(2*d) := by
  obtain ⟨Cs, hCs, hsmall⟩ := exists_bilinear_small_integral_bound d hd
  obtain ⟨Cm, R, hminor⟩ := WeylSums.quadExpSum2_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs + max Cm 0, max R 2, add_nonneg hCs (le_max_right _ _), le_max_right _ _, ?_⟩
  intro L hL a b ξ ζ
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  let f := fun s : ℝ => ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖
  let S := {s : ℝ | |s| ≤ L}
  let T := {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀ * L^(2*γ)}
  let W := {s : ℝ | |s| ≤ T₀ * L^(2*γ)}
  have hf : Continuous f := (WeylSums.continuous_bilinearLatticeSum hLp a b ξ ζ).norm
  have hiS : IntegrableOn f S := by
    rw [show S = Icc (-L) L from abs_window_eq_Icc L]
    exact hf.integrableOn_Icc
  have hiW : IntegrableOn f W := by
    rw [show W = Icc (-(T₀ * L^(2*γ))) (T₀ * L^(2*γ)) from abs_window_eq_Icc _]
    exact hf.integrableOn_Icc
  have hiT : IntegrableOn f T := hiW.mono_set (fun _ h => h.2)
  refine ⟨hiW, ?_⟩
  have hs : MeasurableSet S := by rw [show S = Icc (-L) L from abs_window_eq_Icc L]; exact measurableSet_Icc
  have ht : MeasurableSet T := by
    have h₁ : MeasurableSet {s : ℝ | L ≤ |s|} := measurableSet_le measurable_const measurable_abs
    have h₂ : MeasurableSet {s : ℝ | |s| ≤ T₀ * L^(2*γ)} :=
      measurableSet_le measurable_abs measurable_const
    exact h₁.inter h₂
  have hcover : W ⊆ S ∪ T := by
    intro s hw
    by_cases hs' : |s| ≤ L
    · exact Or.inl hs'
    · exact Or.inr ⟨(not_le.mp hs').le, hw⟩
  have hsBound : (∫ s in S, f s) ≤ Cs * L^(2*d) := by
    apply (setIntegral_mono_on hiS
      (((continuous_const.add continuous_abs).mul hf).integrableOn_Icc.mono_set
        (show S ⊆ Icc (-L) L from fun _ h => abs_le.mp h)) hs ?_).trans (hsmall hL1 a b ξ ζ)
    intro s _
    exact le_mul_of_one_le_left (norm_nonneg _) (by simpa using (abs_nonneg s))
  have hmBound : (∫ s in T, f s) ≤ max Cm 0 * L^(2*d) := by
    have hb := hminor L ((le_max_left _ _).trans hL) a b ξ ζ
    have he : 2*(d : ℝ)-2*((d : ℝ)-1)*(1-γ)+η ≤ ((2*d : ℕ) : ℝ) := by
      push_cast
      linarith only [hηγ]
    calc
      _ ≤ Cm * L^(2*(d : ℝ)-2*((d : ℝ)-1)*(1-γ)+η) := hb
      _ ≤ max Cm 0 * L^(2*(d : ℝ)-2*((d : ℝ)-1)*(1-γ)+η) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hLp.le _)
      _ ≤ max Cm 0 * L^(2*d) := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 he) (le_max_right _ _)
  calc
    _ ≤ ∫ s in S ∪ T, f s := setIntegral_mono_set (hiS.union hiT)
      (ae_of_all _ (fun _ => norm_nonneg _)) (ae_of_all _ (fun _ h => hcover h))
    _ ≤ (∫ s in S, f s) + ∫ s in T, f s :=
      integral_union_le_of_nonneg hs ht f (fun _ => norm_nonneg _) hiS hiT
    _ ≤ Cs * L^(2*d) + max Cm 0 * L^(2*d) := add_le_add hsBound hmBound
    _ = _ := by ring

end WaveTurbulence.SumintPar

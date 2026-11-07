/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CubicSmallIntegral
public import WaveTurbulence.Foundations.SumintPar.IntegralCover
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum3
import Mathlib.Tactic

/-!
# The complete two-time cubic window

The small and large regions are retained separately. Their distinct
powers are needed when combining the cubic factor with the two branches
of the linear estimate, especially near γ=1/2 and in the F23 regime.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- The full cubic window is bounded by the sum of its stationary and Weyl contributions. -/
theorem exists_cubic_global_integral_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ (sel : Bool) (a b c ξ ζ ω : Mom d),
      IntegrableOn (fun st : ℝ × ℝ => ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖)
        {st | |st.1| ≤ T₀*L^(2*γ) ∧ |st.2| ≤ T₀*L^(2*γ)} ∧
      (∫ st : ℝ × ℝ in {st | |st.1| ≤ T₀*L^(2*γ) ∧ |st.2| ≤ T₀*L^(2*γ)},
        ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖) ≤
        Cs * L^(3*d) + Cm * L^(3*(d : ℝ)+γ-2*min γ (1-γ)) * Real.log L := by
  obtain ⟨Cs, hCs, hsmall⟩ := exists_cubic_small_integral_bound d hd
  obtain ⟨Cm, R, hminor⟩ := WeylSums.quadExpSum3_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs, max Cm 0, max (max R 2) (Real.exp 1), hCs, le_max_right _ _, ?_, ?_⟩
  · exact (le_max_right _ _).trans (le_max_left _ _)
  intro L hL sel a b c ξ ζ ω
  have hL2 : 2 ≤ L := (le_max_right R 2).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  let f := fun st : ℝ × ℝ => ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖
  let S := {st : ℝ × ℝ | |st.1| ≤ L ∧ |st.2| ≤ L}
  let T := WeylSums.timeSquareWindow L (T₀*L^(2*γ))
  let W := {st : ℝ × ℝ | |st.1| ≤ T₀*L^(2*γ) ∧ |st.2| ≤ T₀*L^(2*γ)}
  have hf : Continuous f := (WeylSums.continuous_cubicLatticeSum hLp sel a b c ξ ζ ω).norm
  have hiS : IntegrableOn f S := by
    rw [show S = Icc (-L,-L) (L,L) from square_window_eq_Icc L]
    exact hf.integrableOn_Icc
  have hiW : IntegrableOn f W := by
    rw [show W = Icc (-(T₀*L^(2*γ)),-(T₀*L^(2*γ))) (T₀*L^(2*γ),T₀*L^(2*γ)) from
      square_window_eq_Icc _]
    exact hf.integrableOn_Icc
  have hiT : IntegrableOn f T := hiW.mono_set (fun _ h => ⟨h.2.1,h.2.2⟩)
  refine ⟨hiW, ?_⟩
  have hs : MeasurableSet S := by
    rw [show S = Icc (-L,-L) (L,L) from square_window_eq_Icc L]
    exact measurableSet_Icc
  have ht : MeasurableSet T := WeylSums.measurableSet_timeSquareWindow _ _
  have hcover : W ⊆ S ∪ T := by
    intro st hw
    by_cases hh : |st.1| ≤ L ∧ |st.2| ≤ L
    · exact Or.inl hh
    · have hm : L ≤ max |st.1| |st.2| := by
        by_contra hm
        have hm' := max_lt_iff.mp (lt_of_not_ge hm)
        exact hh ⟨hm'.1.le,hm'.2.le⟩
      exact Or.inr ⟨hm,hw⟩
  have hmBound : (∫ st in T, f st) ≤
      max Cm 0 * L^(3*(d : ℝ)+γ-2*min γ (1-γ)) * Real.log L := by
    have hb := hminor L ((le_max_left R 2).trans ((le_max_left _ _).trans hL)) sel a b c ξ ζ ω
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hLp.le _)) hlog)
  calc
    _ ≤ ∫ st in S ∪ T, f st := setIntegral_mono_set (hiS.union hiT)
      (ae_of_all _ (fun _ => norm_nonneg _)) (ae_of_all _ (fun _ h => hcover h))
    _ ≤ (∫ st in S, f st) + ∫ st in T, f st :=
      integral_union_le_of_nonneg hs ht f (fun _ => norm_nonneg _) hiS hiT
    _ ≤ _ := add_le_add (hsmall hL1 sel a b c ξ ζ ω) hmBound

end WaveTurbulence.SumintPar

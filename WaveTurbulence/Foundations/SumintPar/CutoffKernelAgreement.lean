/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CutoffPhaseTranslation
public import WaveTurbulence.Foundations.SumintPar.KernelExtension

/-!
# Pointwise agreement of the actual cutoff phase integral and explicit local kernel

Simultaneous native time translation retains the original static source
inequalities. The exponential rectangle and its inverse reproduce the
actual time integral at every output point in the local time cell.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace WaveTurbulence.SumintPar

/-- Pointwise identity of the translated integrands on the localized output-time cell. -/
theorem shifted_cutoffPhaseSum_indicator_eq {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h t t' t'' : ℝ) (ht : |t-c| ≤ h) (u : D.S.TVar → ℝ) :
    (D.timeDom hI t (t'+t) (t''+t)).indicator (cutoffPhaseSum D L γ δ η p ν r t) (fun v => u v+t) =
      (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) *
        (Real.exp (t-t'-t'') : ℂ)) *
      (localInputTimeDomain D c h).indicator (fun u => cutoffPhaseSum D L γ δ η p ν r 0 u *
        exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI)) ![t,t',t'']) u := by
  classical
  let R := t ∈ Icc (lowerTimeExit D hI u) (upperTimeExit D hI u) ∧
    t' < u (firstTime D hI) ∧ t'' < u (firstTime D hI)
  have hm : (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t) ↔
      u ∈ localInputTimeDomain D c h ∧ R := by
    rw [translated_timeDom_iff_enlarged D hI u t t' t'' c h ht]
    change (_ ∧ _ ∧ R) ↔ ((_ ∧ _) ∧ R)
    tauto
  have hb := exponentialBox_inverse_weight (lowerTimeExit D hI u) (upperTimeExit D hI u)
    (u (firstTime D hI)) ![t,t',t'']
  change (Real.exp (t-t'-t'') : ℂ) *
    exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI)) ![t,t',t''] =
      if R then (1 : ℂ) else 0 at hb
  have hp : cutoffPhaseSum D L γ δ η p ν r t (fun v => u v+t) =
      Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * cutoffPhaseSum D L γ δ η p ν r 0 u := by
    simpa only [zero_add] using cutoffPhaseSum_translate D L γ δ η p ν r 0 t u
  by_cases hh : (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t)
  · obtain ⟨hQ,hR⟩ := hm.mp hh
    rw [Set.indicator_of_mem hh, Set.indicator_of_mem hQ, hp]
    rw [ite_eq_left hR] at hb
    calc
      _ = (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * cutoffPhaseSum D L γ δ η p ν r 0 u) * 1 := by ring
      _ = _ := by rw [← hb]; ring
  · rw [Set.indicator_of_notMem hh]
    by_cases hQ : u ∈ localInputTimeDomain D c h
    · have hR : ¬ R := fun hR => hh (hm.mpr ⟨hQ,hR⟩)
      rw [Set.indicator_of_mem hQ]
      rw [ite_eq_right hR] at hb
      calc
        _ = (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * cutoffPhaseSum D L γ δ η p ν r 0 u) * 0 := by ring
        _ = _ := by rw [← hb]; ring
    · rw [Set.indicator_of_notMem hQ, mul_zero]

/-- The actual source phase integral agrees pointwise with the explicit local ambient extension. -/
theorem cutoffPhaseIntegral_eq_kernelExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h t t' t'' : ℝ) (ht : |t-c| ≤ h) :
    (∫ τ in D.timeDom hI t (t'+t) (t''+t), cutoffPhaseSum D L γ δ η p ν r t τ) =
      (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) *
        (Real.exp (t-t'-t'') : ℂ)) * kernelExtension D hI c h (cutoffPhaseSum D L γ δ η p ν r 0) ![t,t',t''] := by
  rw [← integral_indicator (measurableSet_timeDom D hI t (t'+t) (t''+t))]
  rw [← integral_add_right_eq_self _ (fun _ : D.S.TVar => t)]
  unfold kernelExtension
  rw [← integral_indicator (measurableSet_localInputTimeDomain D c h), ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact shifted_cutoffPhaseSum_indicator_eq D hI L γ δ η p ν r c h t t' t'' ht u

end WaveTurbulence.SumintPar

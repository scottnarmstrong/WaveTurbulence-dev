/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.EnlargedTimeBox
public import WaveTurbulence.Foundations.Sumint.PhaseModulation
public import WaveTurbulence.Foundations.Sumint.ExponentialBoxPointwise
import Mathlib.Tactic

/-!
# A concrete local ambient extension of each source phase integral

The input domain is fixed on each output-time cell. The output dependence
is carried by the explicitly integrable exponential rectangle. Multiplying
by the inverse exponential recovers the source integral at every point of
the cell, rather than merely almost everywhere in the output variables.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The fixed local input domain, retaining all static source inequalities. -/
@[expose] def localInputTimeDomain {d : ℕ} (D : SumintDatum d) (c h : ℝ) : Set (D.S.TVar → ℝ) :=
  enlargedInputTimeBox D c h ∩ staticTimeDomain D

/-- Measurability of the explicit local domain. -/
theorem measurableSet_localInputTimeDomain {d : ℕ} (D : SumintDatum d) (c h : ℝ) :
    MeasurableSet (localInputTimeDomain D c h) :=
  (measurableSet_enlargedInputTimeBox D c h).inter (measurableSet_staticTimeDomain D)

/-- The explicit local extension before restoring the output modulation and inverse exponential. -/
@[expose] noncomputable def localPhaseExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (c h : ℝ)
    (z : Fin 3 → ℝ) : ℂ :=
  ∫ u in localInputTimeDomain D c h,
    D.phase L γ δ η x r 0 u * exponentialBox (lowerTimeExit D hI u)
      (upperTimeExit D hI u) (u (firstTime D hI)) z

/-- Pointwise identity of the translated integrands on the localized output-time cell. -/
theorem shifted_phase_indicator_eq {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d)
    (c h t t' t'' : ℝ) (ht : |t-c| ≤ h) (u : D.S.TVar → ℝ) :
    (D.timeDom hI t (t'+t) (t''+t)).indicator (D.phase L γ δ η x r t) (fun v => u v+t) =
      (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) *
        (Real.exp (t-t'-t'') : ℂ)) *
      (localInputTimeDomain D c h).indicator (fun u => D.phase L γ δ η x r 0 u *
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
  have hp : D.phase L γ δ η x r t (fun v => u v+t) =
      Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * D.phase L γ δ η x r 0 u := by
    simpa only [zero_add] using phase_translate D L γ δ η x r 0 t u
  by_cases hh : (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t)
  · obtain ⟨hQ,hR⟩ := hm.mp hh
    rw [Set.indicator_of_mem hh, Set.indicator_of_mem hQ, hp]
    rw [ite_eq_left hR] at hb
    calc
      _ = (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * D.phase L γ δ η x r 0 u) * 1 := by ring
      _ = _ := by rw [← hb]; ring
  · rw [Set.indicator_of_notMem hh]
    by_cases hQ : u ∈ localInputTimeDomain D c h
    · have hR : ¬ R := fun hR => hh (hm.mpr ⟨hQ,hR⟩)
      rw [Set.indicator_of_mem hQ]
      rw [ite_eq_right hR] at hb
      calc
        _ = (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) * D.phase L γ δ η x r 0 u) * 0 := by ring
        _ = _ := by rw [← hb]; ring
    · rw [Set.indicator_of_notMem hQ, mul_zero]

/-- The actual source phase integral agrees pointwise with the explicit local ambient extension. -/
theorem phaseIntegral_eq_localPhaseExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d)
    (c h t t' t'' : ℝ) (ht : |t-c| ≤ h) :
    (∫ τ in D.timeDom hI t (t'+t) (t''+t), D.phase L γ δ η x r t τ) =
      (Complex.exp ((Real.pi * (∑ v, D.param v) * t : ℝ) * Complex.I) *
        (Real.exp (t-t'-t'') : ℂ)) * localPhaseExtension D hI L γ δ η x r c h ![t,t',t''] := by
  rw [← integral_indicator (measurableSet_timeDom D hI t (t'+t) (t''+t))]
  rw [← integral_add_right_eq_self _ (fun _ : D.S.TVar => t)]
  unfold localPhaseExtension
  rw [← integral_indicator (measurableSet_localInputTimeDomain D c h), ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact shifted_phase_indicator_eq D hI L γ δ η x r c h t t' t'' ht u

end WaveTurbulence.Sumint

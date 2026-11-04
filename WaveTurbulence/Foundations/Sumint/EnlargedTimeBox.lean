/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TranslatedTimeDomain
import Mathlib.Tactic

/-!
# A fixed compact input-time box for each localized output interval

The box is enlarged by exactly h at both endpoints and depends only on
the output-time cell center. On that cell it contains the literal shifted
time domain, which is the pointwise agreement needed for the extension.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The fixed enlarged input box for an output-time cell. -/
@[expose] def enlargedInputTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) : Set (D.S.TVar → ℝ) :=
  Icc (fun v => (D.q v : ℝ)-c-h) (fun v => (D.q v : ℝ)+1-c+h)

/-- The enlarged box is compact in all input-time coordinates. -/
theorem isCompact_enlargedInputTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) :
    IsCompact (enlargedInputTimeBox D c h) := isCompact_Icc

/-- The enlarged box is measurable. -/
theorem measurableSet_enlargedInputTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) :
    MeasurableSet (enlargedInputTimeBox D c h) := measurableSet_Icc

/-- The actual input domain lies in the fixed enlarged box whenever the output time lies in its cell. -/
theorem translated_timeDom_mem_enlargedBox {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (t t' t'' c h : ℝ) (ht : |t-c| ≤ h)
    (hu : (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t)) :
    u ∈ enlargedInputTimeBox D c h := by
  have htc := abs_le.mp ht
  refine ⟨?_, ?_⟩
  · intro v
    have hv := (hu.1 v).1
    dsimp
    linarith only [hv, htc.2]
  · intro v
    have hv := (hu.1 v).2.1
    dsimp
    linarith only [hv, htc.1]

/-- Adding the fixed compact support restriction is an exact pointwise equality on the localized cell. -/
theorem translated_timeDom_iff_enlarged {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (u : D.S.TVar → ℝ) (t t' t'' c h : ℝ) (ht : |t-c| ≤ h) :
    (fun v => u v+t) ∈ D.timeDom hI t (t'+t) (t''+t) ↔
      u ∈ enlargedInputTimeBox D c h ∧ u ∈ staticTimeDomain D ∧
        t ∈ Icc (lowerTimeExit D hI u) (upperTimeExit D hI u) ∧
          t' < u (firstTime D hI) ∧ t'' < u (firstTime D hI) := by
  constructor
  · intro hu
    exact ⟨translated_timeDom_mem_enlargedBox D hI u t t' t'' c h ht hu,
      (translated_timeDom_iff D hI u t t' t'').mp hu⟩
  · intro hu
    exact (translated_timeDom_iff D hI u t t' t'').mpr hu.2

end WaveTurbulence.Sumint

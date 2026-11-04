/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.OrderedPairFactors

/-!
# Measurability of the retained ordering factors

The middle time is a parameter in a closed ordering strip. Pair norms
and their gap amplitudes are measurable jointly with this parameter,
so the exact grouped-time Tonelli theorem applies.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Every pair gap amplitude is nonnegative at every real exponent. -/
theorem pairGapAmplitude_nonneg {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) :
    0 ≤ pairGapAmplitude D η a z := by
  unfold pairGapAmplitude
  split_ifs
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact zero_le_one

/-- Retaining the ordering restriction preserves nonnegativity. -/
theorem orderedPairNorm_nonneg {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) :
    0 ≤ orderedPairNorm D L γ δ η p ν r t u a z := by
  unfold orderedPairNorm
  split_ifs <;> first
    | exact mul_nonneg (pairGapAmplitude_nonneg D η a z) (norm_nonneg _)
    | exact le_rfl

/-- Joint measurability in the fixed distinguished times and the pair-time tuple. -/
theorem measurable_orderedPairNorm {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    Measurable (fun x : (Fin D.S.I → ℝ) × (ℝ × ℝ) =>
      orderedPairNorm D L γ δ η p ν r t x.1 a x.2) := by
  have hb : Measurable (fun z : ℝ × ℝ => pairGapAmplitude D η a z*
      ‖pairTimeSum D L γ δ p ν r t a z‖) :=
    (measurable_pairGapAmplitude D η a).mul (measurable_pairTimeSum_norm D hL γ δ p ν r t a)
  by_cases ha : caseAPair D a
  · simp only [orderedPairNorm,ite_eq_left ha]
    apply Measurable.ite
    · have hl : Measurable (fun x : (Fin D.S.I → ℝ) × (ℝ × ℝ) => |x.2.1-x.1 a.1|) := by fun_prop
      have hr : Measurable (fun x : (Fin D.S.I → ℝ) × (ℝ × ℝ) => |x.2.1-x.2.2|) := by fun_prop
      exact measurableSet_le hl hr
    · exact hb.comp measurable_snd
    · exact measurable_const
  · simp only [orderedPairNorm,ite_eq_right ha]
    exact hb.comp measurable_snd

/-- The actual distinguished linear norm is measurable in its one time. -/
theorem measurable_linearTimeSum_norm {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : Fin D.S.I) : Measurable (fun s : ℝ => ‖linearTimeSum D L γ δ p ν r t i s‖) := by
  have hv : Measurable (fun s : ℝ => ![s]) := by fun_prop
  have hm := (measurable_plainTimeNormFactor D hL γ δ p ν r t (.inl i)).comp hv
  change Measurable (fun s : ℝ => ‖linearTimeSum D L γ δ p ν r t i ((![s]) 0)‖) at hm
  simpa only [Matrix.cons_val_zero] using hm

/-- The actual normal factor norm is measurable in its three local times. -/
theorem measurable_normalTimeSum_norm {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    Measurable (fun z : Fin 3 → ℝ => ‖normalTimeSum D L γ δ p ν r t i z‖) :=
  measurable_plainTimeNormFactor D hL γ δ p ν r t (.inr (.inr i))

end WaveTurbulence.Sumint

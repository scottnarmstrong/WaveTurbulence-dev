/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorRegularity
public import WaveTurbulence.Foundations.SumintPar.TimeFactorFubini

/-!
# Exact integration of the source factor norms over an input box

Coordinatewise interval restrictions regroup with the same measure as
the source time variables. This yields an equality of nonnegative masses
before the additional static order constraints are used for bad gains.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- The local box belonging to one independent factor. -/
@[expose] def localFactorBox (S : SumintShape) (lo hi : S.TVar → ℝ) (a : FactorIdx S) :
    Set (FactorCoordinate S a → ℝ) :=
  Icc (fun j => lo (factorCoordinateTimeEquiv S ⟨a,j⟩))
    (fun j => hi (factorCoordinateTimeEquiv S ⟨a,j⟩))

/-- General coordinate evaluation of the source grouping. -/
theorem timeCoordinateGrouping_apply (S : SumintShape) (τ : S.TVar → ℝ)
    (a : FactorIdx S) (j : FactorCoordinate S a) :
    timeCoordinateGrouping S τ a j = τ (factorCoordinateTimeEquiv S ⟨a,j⟩) := by
  rcases a with i | (p | i)
  · fin_cases j
    rfl
  · fin_cases j <;> rfl
  · rfl

/-- A source box is exactly the product of its independent local boxes. -/
theorem mem_input_box_iff_local_boxes (S : SumintShape) (lo hi τ : S.TVar → ℝ) :
    τ ∈ Icc lo hi ↔ ∀ a : FactorIdx S,
      timeCoordinateGrouping S τ a ∈ localFactorBox S lo hi a := by
  constructor
  · intro h a
    constructor
    · intro j
      change lo (factorCoordinateTimeEquiv S ⟨a,j⟩) ≤ timeCoordinateGrouping S τ a j
      rw [timeCoordinateGrouping_apply]
      exact h.1 _
    · intro j
      change timeCoordinateGrouping S τ a j ≤ hi (factorCoordinateTimeEquiv S ⟨a,j⟩)
      rw [timeCoordinateGrouping_apply]
      exact h.2 _
  · intro h
    constructor
    · intro v
      obtain ⟨⟨a,j⟩,rfl⟩ := (factorCoordinateTimeEquiv S).surjective v
      have hh := (h a).1 j
      simpa only [timeCoordinateGrouping_apply] using hh
    · intro v
      obtain ⟨⟨a,j⟩,rfl⟩ := (factorCoordinateTimeEquiv S).surjective v
      have hh := (h a).2 j
      simpa only [timeCoordinateGrouping_apply] using hh

/-- Every source norm factor is nonnegative, including its gap multiplier. -/
theorem sourceTimeNormFactor_nonneg {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ) :
    0 ≤ sourceTimeNormFactor D L γ δ η p ν r t a z := by
  apply mul_nonneg _ _
  · rcases a with i | (a | i)
    · exact zero_le_one
    · change 0 ≤ pairGapAmplitude D η a (z 0,z 1)
      unfold pairGapAmplitude
      split_ifs
      · exact Real.rpow_nonneg (abs_nonneg _) _
      · exact zero_le_one
    · exact zero_le_one
  · rcases a with i | (a | i) <;> exact norm_nonneg _

/-- TARGET sumint Step 2: the actual source box mass factors exactly. -/
theorem lintegral_box_norm_cutoffPhaseSum_eq {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (lo hi : D.S.TVar → ℝ) :
    (∫⁻ τ in Icc lo hi, ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) =
      ∏ a : FactorIdx D.S, ∫⁻ z in localFactorBox D.S lo hi a,
        ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a z) := by
  classical
  let f := fun (a : FactorIdx D.S) =>
    (localFactorBox D.S lo hi a).indicator
      (fun z => ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a z))
  have hf (a : FactorIdx D.S) : Measurable (f a) :=
    (ENNReal.measurable_ofReal.comp (measurable_sourceTimeNormFactor D hL γ δ η p ν r t a)).indicator
      measurableSet_Icc
  have he (τ : D.S.TVar → ℝ) :
      (Icc lo hi).indicator (fun τ => ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) τ =
        ∏ a : FactorIdx D.S, f a (timeCoordinateGrouping D.S τ a) := by
    by_cases hτ : τ ∈ Icc lo hi
    · have hm := (mem_input_box_iff_local_boxes D.S lo hi τ).mp hτ
      rw [indicator_of_mem hτ,← ofReal_norm,norm_cutoffPhaseSum_eq_time_factor_product D hL γ δ η p ν r t τ,
        ENNReal.ofReal_prod_of_nonneg (fun a _ => sourceTimeNormFactor_nonneg D L γ δ η p ν r t a _)]
      apply Finset.prod_congr rfl
      intro a _
      dsimp only [f]
      rw [indicator_of_mem (hm a)]
    · have hm : ¬ ∀ a : FactorIdx D.S,
          timeCoordinateGrouping D.S τ a ∈ localFactorBox D.S lo hi a :=
        fun hh => hτ ((mem_input_box_iff_local_boxes D.S lo hi τ).mpr hh)
      push Not at hm
      obtain ⟨a,ha⟩ := hm
      rw [indicator_of_notMem hτ]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ a) (indicator_of_notMem ha _)
  rw [← lintegral_indicator measurableSet_Icc]
  simp_rw [he]
  rw [lintegral_time_factor_product D.S f hf]
  apply Finset.prod_congr rfl
  intro a _
  exact lintegral_indicator measurableSet_Icc _

end WaveTurbulence.SumintPar

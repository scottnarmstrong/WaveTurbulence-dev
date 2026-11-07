/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.OrderedPairRegularity
public import WaveTurbulence.Foundations.SumintPar.GroupedTimeBoxes

/-!
# Reducing the actual static-domain mass to ordered independent factors

Only the case-(a) first-pair strips are retained when discarding static
constraints. Pair integration is performed with all distinguished times
fixed, exactly as required by the uniform ordering-strip estimates.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- The nonnegative grouped product with precisely the retained first-pair restrictions. -/
@[expose] noncomputable def groupedOrderedSourceNorm {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (z : GroupedTimes D.S) : ℝ :=
  (∏ i : Fin D.S.I, ‖linearTimeSum D L γ δ p ν r t i (z.1 i)‖) *
  (∏ a : Σ i : Fin D.S.I, Fin (D.S.m i), orderedPairNorm D L γ δ η p ν r t z.1 a (z.2.1 a)) *
  (∏ i : {i : Fin D.S.I // D.S.nor i = true}, ‖normalTimeSum D L γ δ p ν r t i (z.2.2 i)‖)

/-- The ordered grouped product is measurable in its actual grouped product measure. -/
theorem measurable_groupedOrderedSourceNorm {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) :
    Measurable (groupedOrderedSourceNorm D L γ δ η p ν r t) := by
  unfold groupedOrderedSourceNorm
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      exact (measurable_linearTimeSum_norm D hL γ δ p ν r t i).comp
        ((measurable_pi_apply i).comp measurable_fst)
    · apply Finset.measurable_prod
      intro a _
      have hp : Measurable (fun z : GroupedTimes D.S => (z.1,z.2.1 a)) := by fun_prop
      exact (measurable_orderedPairNorm D hL γ δ η p ν r t a).comp hp
  · apply Finset.measurable_prod
    intro i _
    have hn : Measurable (fun z : GroupedTimes D.S => z.2.2 i) := by fun_prop
    exact (measurable_normalTimeSum_norm D hL γ δ p ν r t i).comp hn

/-- On the exact source static domain the retained pair restrictions do not change the norm. -/
theorem groupedOrderedSourceNorm_eq_on_static {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (hτ : τ ∈ staticTimeDomain D) :
    groupedOrderedSourceNorm D L γ δ η p ν r t (measurableTimeGrouping D.S τ) =
      groupedSourceNorm D L γ δ η p ν r t (measurableTimeGrouping D.S τ) := by
  unfold groupedOrderedSourceNorm groupedSourceNorm
  apply congrArg (fun B : ℝ =>
    (∏ i : Fin D.S.I, ‖linearTimeSum D L γ δ p ν r t i ((measurableTimeGrouping D.S τ).1 i)‖)*B*
      (∏ i : {i : Fin D.S.I // D.S.nor i = true},
        ‖normalTimeSum D L γ δ p ν r t i ((measurableTimeGrouping D.S τ).2.2 i)‖))
  apply Finset.prod_congr rfl
  intro a _
  exact orderedPairNorm_eq_on_static D hD δ p ν r t τ hτ a

/-- TARGET sumint Step 2: the actual local input mass is bounded by the explicit ordered product integral. -/
theorem lintegral_static_box_cutoffPhaseSum_le_grouped {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) :
    (∫⁻ τ in Icc lo hi ∩ staticTimeDomain D, ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) ≤
      ∫⁻ u in linearFamilyBox D.S lo hi,
        ∫⁻ q in pairFamilyBox D.S lo hi,
          ∫⁻ n in normalFamilyBox D.S lo hi,
            ENNReal.ofReal (groupedOrderedSourceNorm D L γ δ η p ν r t (u,q,n)) := by
  calc
    _ = ∫⁻ τ in Icc lo hi ∩ staticTimeDomain D,
        ENNReal.ofReal (groupedOrderedSourceNorm D L γ δ η p ν r t (measurableTimeGrouping D.S τ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Icc.inter (measurableSet_staticTimeDomain D))] with τ hτ
      rw [← ofReal_norm,norm_cutoffPhaseSum_eq_groupedSourceNorm D hL γ δ η p ν r t,
        groupedOrderedSourceNorm_eq_on_static D hD δ p ν r t τ hτ.2]
    _ ≤ ∫⁻ τ in Icc lo hi,
        ENNReal.ofReal (groupedOrderedSourceNorm D L γ δ η p ν r t (measurableTimeGrouping D.S τ)) :=
      lintegral_mono_set inter_subset_left
    _ = _ := lintegral_input_box_grouped D.S lo hi _
      (ENNReal.measurable_ofReal.comp (measurable_groupedOrderedSourceNorm D hL γ δ η p ν r t))

end WaveTurbulence.SumintPar

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CoreWindowProduct

/-!
# Full core masses after discarding only the ordering strip

This auxiliary upper bound keeps the literal old-factor windows and
oscillatory masses. The ordered first bad core uses a separate stronger
estimate; it is not replaced by this unrestricted bound.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The literal full interval mass of an old source norm factor. -/
@[expose] noncomputable def oldFactorWindowMass {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (a : FactorIdx D.S) : ℝ≥0∞ :=
  ∫⁻ z in oldFactorTimeBox D c h a, ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a z)

/-- Discarding a core's ordering strip gives the product of its actual old-factor interval masses. -/
theorem lintegral_sourceCore_le_unordered {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (b : FactorIdx D.S) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z) ≤
      sourceCoreMultiplier D r b *
        ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, oldFactorWindowMass D L γ δ η p ν r t c h a.1 := by
  let f (a : FactorIdx D.S) := (oldFactorTimeBox D c h a).indicator
    (fun z => ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a z))
  have hf (a : FactorIdx D.S) : Measurable (f a) :=
    (measurable_sourceTimeNormFactor D hL γ δ η p ν r t a).ennreal_ofReal.indicator
      (measurableSet_oldFactorTimeBox D c h a)
  calc
    _ ≤ ∫⁻ z, sourceCoreMultiplier D r b *
        ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, f a.1 (sourceCoreOldTimes D b z a) := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ sourceCoreTimeBox D c h b ∩ {z | sourceCoreOrdering D b z}
      · rw [sourceCoreNormFactor,Set.indicator_of_mem hz]
        apply le_of_eq
        congr 1
        apply Finset.prod_congr rfl
        intro a _
        exact (Set.indicator_of_mem ((mem_sourceCoreTimeBox_iff D c h b z).mp hz.1 a)
          (fun y => ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a.1 y))).symm
      · rw [sourceCoreNormFactor,Set.indicator_of_notMem hz]
        exact bot_le
    _ = sourceCoreMultiplier D r b *
        ∫⁻ z, ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, f a.1 (sourceCoreOldTimes D b z a) :=
      lintegral_const_mul _ (by
        apply Finset.measurable_prod
        intro a _
        exact (hf a.1).comp (measurable_sourceCoreOldTimes D b a))
    _ = _ := by
      rw [lintegral_sourceCoreOldTimes_product D b _ (fun a => hf a.1)]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact lintegral_indicator (measurableSet_oldFactorTimeBox D c h a.1) _

end WaveTurbulence.Sumint

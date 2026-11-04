/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreProduct
public import WaveTurbulence.Foundations.Sumint.SourceCoreMeasure
public import WaveTurbulence.Foundations.Sumint.FixedCoordinateTrace
public import WaveTurbulence.Foundations.Sumint.SourceExitAmplitude

/-!
# Actual endpoint traces reduce to independent concrete core masses

The source endpoint amplitude has modulus at most the weighted source
input on its actual domain. Fixing any injective list of native times
then leaves a product of explicit core integrals under fixed/free
coordinate measures. This reduction requires no source trace bound as
a hypothesis.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual endpoint coefficient, extended by zero off the local static domain. -/
@[expose] noncomputable def sourceExitInput {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) : (D.S.TVar → ℝ) → ℂ :=
  (localInputTimeDomain D c h).indicator
    (sourceExitAmplitude D hI upper v (weightedCutoffInput D L γ δ η p ν r))

/-- The zero-extended actual endpoint coefficient is measurable. -/
theorem measurable_sourceExitInput {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (c h : ℝ) (upper : Bool) (v : D.S.TVar) :
    Measurable (sourceExitInput D hI L γ δ η p ν r c h upper v) :=
  (measurable_sourceExitAmplitude D hI upper v _
    (measurable_weightedCutoffInput D hL γ δ η p ν r)).indicator
      (measurableSet_localInputTimeDomain D c h)

/-- The actual selected endpoint norm is bounded by the independent concrete core product. -/
theorem enorm_sourceExitInput_le_core_product {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) :
    ‖sourceExitInput D hI L γ δ η p ν r c h upper v u‖ₑ ≤
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
        ∏ b, sourceCoreNormFactor D L γ δ η p ν r 0 c h b (sourceCoreTimeGrouping D u b) := by
  apply le_trans ?_ (weightedCutoffInput_indicator_le_core_product D hD hL δ p ν r c h u)
  by_cases hu : u ∈ localInputTimeDomain D c h
  · simp only [sourceExitInput,Set.indicator_of_mem hu]
    rw [← ofReal_norm,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_sourceExitAmplitude_le D hI upper v _ u (fun w => (hu.2.1 w).le))
  · simp only [sourceExitInput,Set.indicator_of_notMem hu,enorm_zero]
    exact le_rfl

noncomputable section

local instance {d : ℕ} (D : SumintDatum d) {k : ℕ} (sel : Fin k → D.S.TVar) :
    Fintype {i : D.S.TVar // i ∉ Set.range sel} :=
  @Subtype.fintype D.S.TVar (fun i => i ∉ Set.range sel) (fun _ => Classical.propDecidable _) inferInstance

/-- Fixing actual native times reduces their remaining-coordinate trace to explicit independent core masses. -/
theorem lintegral_sourceExitInput_trace_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) {k : ℕ}
    (sel : Fin k → D.S.TVar) (hsel : Function.Injective sel) (x : Fin k → ℝ) :
    (∫⁻ y : {i : D.S.TVar // i ∉ Set.range sel} → ℝ,
      ‖sourceExitInput D hI L γ δ η p ν r c h upper v ((selectedCoordinateSplit sel hsel).symm (x,y))‖ₑ) ≤
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
      ∏ b : FactorIdx D.S, ∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r 0 c h b z
        ∂Measure.pi (fun j => fixedCoordinateMeasure (Set.range sel) (selectedFixedVector sel hsel x)
          (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩)) := by
  calc
    _ = ∫⁻ u, ‖sourceExitInput D hI L γ δ η p ν r c h upper v u‖ₑ
        ∂Measure.pi (fixedCoordinateMeasure (Set.range sel) (selectedFixedVector sel hsel x)) :=
      by
        convert (lintegral_fixedCoordinateTrace_eq sel hsel x _
          (measurable_sourceExitInput D hI hL γ δ η p ν r c h upper v).enorm).symm using 1
        congr 3
        exact Subsingleton.elim _ _
    _ ≤ ∫⁻ u, ENNReal.ofReal (sourceWeightDecay D L γ η)*
        ∏ b, sourceCoreNormFactor D L γ δ η p ν r 0 c h b (sourceCoreTimeGrouping D u b)
        ∂Measure.pi (fixedCoordinateMeasure (Set.range sel) (selectedFixedVector sel hsel x)) :=
      lintegral_mono (enorm_sourceExitInput_le_core_product D hI hD hL δ p ν r c h upper v)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by finiteness),lintegral_sourceCore_product D _ _
        (measurable_sourceCoreNormFactor D hL γ δ η p ν r 0 c h)]

end

end WaveTurbulence.Sumint

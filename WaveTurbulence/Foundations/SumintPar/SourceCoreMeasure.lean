/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreArity
public import WaveTurbulence.Foundations.SumintPar.CoordinateGroupingMeasure
public import WaveTurbulence.Foundations.SumintPar.FixedCoordinateMeasure

/-!
# Actual coarse source Fubini with fixed and free coordinate measures

Regrouping works for arbitrary sigma-finite native coordinate measures.
If a coarse core is untouched by the selected source times, every one
of its coordinate measures is exactly Lebesgue measure. Thus its
ordinary source window estimate remains available unchanged.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Native time-to-core label, retaining the original coordinate lookup. -/
@[expose] noncomputable def sourceTimeCore {d : ℕ} (D : SumintDatum d) (v : D.S.TVar) : FactorIdx D.S :=
  sourceCoreGroup D (timeFactorCoordinate D.S v).1

/-- Every coarse coordinate has precisely its own coarse source label. -/
theorem sourceTimeCore_coordinate {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b) :
    sourceTimeCore D (sourceCoreCoordinateTimeEquiv D ⟨b,z⟩) = b := by
  rcases z with ⟨⟨a,ha⟩,j⟩
  exact (congrArg (fun q : (Σ a : FactorIdx D.S, FactorCoordinate D.S a) => sourceCoreGroup D q.1)
    ((factorCoordinateTimeEquiv D.S).left_inv ⟨a,j⟩)).trans ha

/-- The actual core grouping preserves arbitrary sigma-finite source coordinate measures. -/
theorem measurePreserving_sourceCoreTimeGrouping {d : ℕ} (D : SumintDatum d)
    (μ : D.S.TVar → Measure ℝ) [∀ v, SigmaFinite (μ v)] :
    MeasurePreserving (sourceCoreTimeGrouping D) (Measure.pi μ)
      (Measure.pi fun b => Measure.pi fun z => μ (sourceCoreCoordinateTimeEquiv D ⟨b,z⟩)) :=
  measurePreserving_coordinateGrouping (sourceCoreCoordinateTimeEquiv D) μ

/-- Exact source-core Fubini also holds with selected coordinates fixed by point masses. -/
theorem lintegral_sourceCore_product {d : ℕ} (D : SumintDatum d)
    (μ : D.S.TVar → Measure ℝ) [∀ v, SigmaFinite (μ v)]
    (f : (b : FactorIdx D.S) → (SourceCoreCoordinate D b → ℝ) → ℝ≥0∞)
    (hf : ∀ b, Measurable (f b)) :
    (∫⁻ u, ∏ b, f b (sourceCoreTimeGrouping D u b) ∂Measure.pi μ) =
      ∏ b, ∫⁻ z, f b z ∂Measure.pi (fun j => μ (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩)) := by
  have he := (measurePreserving_sourceCoreTimeGrouping D μ).lintegral_comp_emb
    (sourceCoreTimeGrouping D).measurableEmbedding (fun z => ∏ b, f b (z b))
  rw [he]
  exact lintegral_fintype_prod_eq_prod (FactorIdx D.S) f hf

/-- Every coordinate measure in an untouched coarse core is the ordinary Lebesgue measure. -/
theorem fixedCoordinateMeasure_core_eq_volume {d : ℕ} (D : SumintDatum d)
    (s : Finset D.S.TVar) (x : D.S.TVar → ℝ) (b : FactorIdx D.S) (hb : b ∉ sourceExitCores D s)
    (z : SourceCoreCoordinate D b) :
    fixedCoordinateMeasure (s:Set D.S.TVar) x (sourceCoreCoordinateTimeEquiv D ⟨b,z⟩) = volume := by
  unfold fixedCoordinateMeasure
  apply ite_eq_right
  intro hv
  apply hb
  exact Finset.mem_image.mpr ⟨sourceCoreCoordinateTimeEquiv D ⟨b,z⟩,hv,sourceTimeCore_coordinate D b z⟩

end WaveTurbulence.SumintPar

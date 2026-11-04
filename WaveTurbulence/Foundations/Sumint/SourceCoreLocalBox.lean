/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreDomain
public import WaveTurbulence.Foundations.Sumint.FixedCoordinateBoxIntegral

/-!
# Native interval bounds inside one concrete source core

Every old factor in a core reads exactly the corresponding native
intervals. The entire core vanishes off that box, whose mixed fixed/free
mass is bounded by three to its unchanged coordinate count.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- Projecting a core box gives the literal old-factor source intervals. -/
theorem sourceCoreOldTimes_mem_intervals {d : ℕ} (D : SumintDatum d) (c h : ℝ)
    (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) (hz : z ∈ sourceCoreTimeBox D c h b)
    (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) (j : FactorCoordinate D.S a.1) :
    sourceCoreOldTimes D b z a j ∈ Icc
      (enlargedTimeLower D c h (factorCoordinateTime D.S ⟨a.1,j⟩))
      (enlargedTimeUpper D c h (factorCoordinateTime D.S ⟨a.1,j⟩)) :=
  hz ⟨a,j⟩ (Set.mem_univ _)

/-- The concrete core factor vanishes outside its native interval box. -/
theorem sourceCoreNormFactor_eq_zero_off_box {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) (hz : z ∉ sourceCoreTimeBox D c h b) :
    sourceCoreNormFactor D L γ δ η p ν r t c h b z = 0 := by
  exact Set.indicator_of_notMem (fun hs => hz hs.1) _

/-- Any proved pointwise core bound yields its actual fixed/free mass bound. -/
theorem lintegral_sourceCore_fixed_le {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
    {h : ℝ} (hh : h ≤ 1) (b : FactorIdx D.S) (s : Set D.S.TVar) (x : D.S.TVar → ℝ)
    (K : ℝ≥0∞) (hK : ∀ z ∈ sourceCoreTimeBox D c h b,
      sourceCoreNormFactor D L γ δ η p ν r t c h b z ≤ K) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure s x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
      K*ENNReal.ofReal (3^(sourceCoreArity D b):ℝ) := by
  apply lintegral_fixedCoordinate_box_le s x _ _ _ _ _ K hK
    (sourceCoreNormFactor_eq_zero_off_box D L γ δ η p ν r t c h b)
  intro j
  dsimp [enlargedTimeUpper,enlargedTimeLower]
  linarith only [hh]

end WaveTurbulence.Sumint

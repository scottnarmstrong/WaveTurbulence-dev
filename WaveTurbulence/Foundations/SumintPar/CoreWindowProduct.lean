/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CoreOldFactorIntegral

/-!
# Native old-factor windows inside a coarse source core

The coarse interval mask equals the product of its unchanged old-factor
interval masks. Discarding only the additional ordering mask gives a
full-mass bound, sufficient for all cores without a case-(a) strip.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The literal enlarged interval box for one old source factor. -/
@[expose] def oldFactorTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) (a : FactorIdx D.S) :
    Set (FactorCoordinate D.S a → ℝ) :=
  Set.pi Set.univ (fun j => Icc (enlargedTimeLower D c h (factorCoordinateTime D.S ⟨a,j⟩))
    (enlargedTimeUpper D c h (factorCoordinateTime D.S ⟨a,j⟩)))

/-- Each old source time box is measurable. -/
theorem measurableSet_oldFactorTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) (a : FactorIdx D.S) :
    MeasurableSet (oldFactorTimeBox D c h a) :=
  MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Icc)

/-- The core interval condition is exactly all unchanged old-factor interval conditions. -/
theorem mem_sourceCoreTimeBox_iff {d : ℕ} (D : SumintDatum d) (c h : ℝ)
    (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) :
    z ∈ sourceCoreTimeBox D c h b ↔
      ∀ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, sourceCoreOldTimes D b z a ∈ oldFactorTimeBox D c h a.1 := by
  constructor
  · intro hz a j _
    exact sourceCoreOldTimes_mem_intervals D c h b z hz a j
  · intro hz j _
    rcases j with ⟨a,j⟩
    exact hz a j (Set.mem_univ _)

/-- The product of old-factor masks equals their concrete core mask. -/
theorem prod_oldFactor_indicator_eq {d : ℕ} (D : SumintDatum d) (c h : ℝ)
    (b : FactorIdx D.S)
    (f : (a : FactorIdx D.S) → (FactorCoordinate D.S a → ℝ) → ℝ≥0∞)
    (z : SourceCoreCoordinate D b → ℝ) :
    (∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b},
      (oldFactorTimeBox D c h a.1).indicator (f a.1) (sourceCoreOldTimes D b z a)) =
      (sourceCoreTimeBox D c h b).indicator
        (fun z => ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, f a.1 (sourceCoreOldTimes D b z a)) z := by
  by_cases hz : z ∈ sourceCoreTimeBox D c h b
  · rw [Set.indicator_of_mem hz]
    apply Finset.prod_congr rfl
    intro a _
    exact Set.indicator_of_mem ((mem_sourceCoreTimeBox_iff D c h b z).mp hz a) _
  · rw [Set.indicator_of_notMem hz]
    obtain ⟨a,ha⟩ := not_forall.mp (fun hh => hz ((mem_sourceCoreTimeBox_iff D c h b z).mpr hh))
    exact Finset.prod_eq_zero (Finset.mem_univ a) (Set.indicator_of_notMem ha _)

end WaveTurbulence.SumintPar

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

end WaveTurbulence.SumintPar

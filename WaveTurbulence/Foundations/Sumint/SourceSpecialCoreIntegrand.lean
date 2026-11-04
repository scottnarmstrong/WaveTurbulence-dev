/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialCoreMasks

/-!
# The actual first bad core keeps its ordered pair integrand

After the exact native grouping, the concrete core is bounded by the
linear norm times the original ordered pair norm on the three literal
source intervals. The strip is retained before any integration.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- First bad cores have no external case-(b) multiplier. -/
theorem sourceCoreMultiplier_special {d : ℕ} (D : SumintDatum d) (r : Mom d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    sourceCoreMultiplier D r (.inl a.1) = 1 := by
  change caseBMultiplier D r a.1 = 1
  rcases ha with ha | ha
  · simp only [caseBMultiplier,ha.2.1]
    norm_num
  · simp only [caseBMultiplier,ha.2.1]
    norm_num

/-- The actual first bad core's grouped integrand retains its native ordered pair restriction. -/
theorem sourceCoreNormFactor_special_le {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) (z : Fin 3 → ℝ) :
    sourceCoreNormFactor D L γ δ η p ν r t c h (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) ≤
      (Icc (fun j => enlargedTimeLower D c h (sourceSpecialTime D a j))
        (fun j => enlargedTimeUpper D c h (sourceSpecialTime D a j))).indicator
        (fun z => ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t a.1 (z 2)‖ *
          ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t (fun _ => z 2) a (z 0,z 1))) z := by
  by_cases hz : (sourceSpecialCoreGrouping D a ha).symm z ∈
      sourceCoreTimeBox D c h (.inl a.1) ∩ {z | sourceCoreOrdering D (.inl a.1) z}
  · rw [sourceCoreNormFactor,Set.indicator_of_mem hz,sourceCoreMultiplier_special D r a ha,one_mul,
      sourceCoreRawNorm_special_grouped D L γ δ η p ν r t a ha,
      Set.indicator_of_mem ((sourceSpecialCoreGrouping_mem_box D a ha c h z).mp hz.1)]
    apply le_of_eq
    congr 2
    unfold orderedPairNorm
    by_cases hca : caseAPair D a
    · simp only [ite_eq_left hca,ite_eq_left (sourceSpecialCoreOrdering_strip D a ha z hz.2 hca)]
    · simp only [ite_eq_right hca]
  · rw [sourceCoreNormFactor,Set.indicator_of_notMem hz]
    exact bot_le

end WaveTurbulence.Sumint

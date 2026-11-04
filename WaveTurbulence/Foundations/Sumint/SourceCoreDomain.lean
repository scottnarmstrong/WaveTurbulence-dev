/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreNormFactor
public import WaveTurbulence.Foundations.Sumint.OrderedPairFactors

/-!
# The actual local source domain satisfies all coarse interval and ordering masks

Every coarse coordinate remains at its native source time. The actual
static case-(a) constraints imply the local middle-time strips, including
when those times are read through the one-core reconstruction.
-/

public section

open MeasureTheory Set
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Every coarse coordinate of a grouped actual input vector is its native input time. -/
theorem sourceCoreTimeGrouping_coordinate {d : ℕ} (D : SumintDatum d) (u : D.S.TVar → ℝ)
    (b : FactorIdx D.S) (j : SourceCoreCoordinate D b) :
    sourceCoreTimeGrouping D u b j = u (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩) := by
  rcases j with ⟨⟨a,ha⟩,k⟩
  exact sourceCoreTimeGrouping_apply D u b a ha k

/-- A one-core reconstruction of an actual grouped vector restores each old factor time in that core. -/
theorem sourceCoreLocalInput_grouped_factorCoordinate {d : ℕ} (D : SumintDatum d)
    (u : D.S.TVar → ℝ) (b : FactorIdx D.S) (a : FactorIdx D.S)
    (ha : sourceCoreGroup D a = b) (j : FactorCoordinate D.S a) :
    sourceCoreLocalInput D b (sourceCoreTimeGrouping D u b) (factorCoordinateTime D.S ⟨a,j⟩) =
      u (factorCoordinateTime D.S ⟨a,j⟩) :=
  (sourceCoreLocalInput_factorCoordinate D b _ a ha j).trans (sourceCoreTimeGrouping_apply D u b a ha j)

/-- The actual enlarged input box implies every coarse native interval mask. -/
theorem sourceCoreTimeGrouping_mem_box {d : ℕ} (D : SumintDatum d) (c h : ℝ)
    (u : D.S.TVar → ℝ) (hu : u ∈ enlargedInputTimeBox D c h) (b : FactorIdx D.S) :
    sourceCoreTimeGrouping D u b ∈ sourceCoreTimeBox D c h b := by
  intro j _
  rw [sourceCoreTimeGrouping_coordinate]
  exact ⟨hu.1 _,hu.2 _⟩

/-- The actual admissible source ordering implies every coarse case-(a) mask. -/
theorem sourceCoreOrdering_grouped {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (u : D.S.TVar → ℝ) (hu : u ∈ staticTimeDomain D) (b : FactorIdx D.S) :
    sourceCoreOrdering D b (sourceCoreTimeGrouping D u b) := by
  intro a ha hb
  have hg : sourceCoreGroup D (.inr (.inl a)) = .inl a.1 := by
    rw [sourceCoreGroup,ite_eq_left (Or.inl ha)]
  have hl : sourceCoreGroup D (.inl a.1) = b := hg.symm.trans hb
  have ho := sourceCoreLocalInput_grouped_factorCoordinate D u b (.inr (.inl a)) hb 0
  have hi := sourceCoreLocalInput_grouped_factorCoordinate D u b (.inr (.inl a)) hb 1
  have hm := sourceCoreLocalInput_grouped_factorCoordinate D u b (.inl a.1) hl 0
  change sourceCoreLocalInput D b (sourceCoreTimeGrouping D u b) (.inl ⟨a.1,a.2.succ⟩) =
    u (.inl ⟨a.1,a.2.succ⟩) at ho
  change sourceCoreLocalInput D b (sourceCoreTimeGrouping D u b) (.inr (.inl a)) = u (.inr (.inl a)) at hi
  change sourceCoreLocalInput D b (sourceCoreTimeGrouping D u b) (.inl ⟨a.1,0⟩) = u (.inl ⟨a.1,0⟩) at hm
  rw [ho,hi,hm]
  exact source_case_a_pair_strip D hD u hu a ha

/-- All concrete core masks equal one on the actual local source domain. -/
theorem sourceCoreNormFactor_eq_on_local {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (u : D.S.TVar → ℝ) (hu : u ∈ localInputTimeDomain D c h) (b : FactorIdx D.S) :
    sourceCoreNormFactor D L γ δ η p ν r t c h b (sourceCoreTimeGrouping D u b) =
      sourceCoreMultiplier D r b*sourceCoreRawNorm D L γ δ η p ν r t b (sourceCoreTimeGrouping D u b) := by
  apply Set.indicator_of_mem
  exact ⟨sourceCoreTimeGrouping_mem_box D c h u hu.1 b,sourceCoreOrdering_grouped D hD u hu.2 b⟩

end WaveTurbulence.Sumint

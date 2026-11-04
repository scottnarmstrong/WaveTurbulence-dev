/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreLocalInput
public import WaveTurbulence.Foundations.Sumint.SourceCaseBProducts
public import WaveTurbulence.Foundations.Sumint.SourceBoxFactorization
public import WaveTurbulence.Foundations.Sumint.SourceMassWindows

/-!
# Concrete nonnegative factors on the coarse source cores

Each factor contains exactly its old oscillatory norm factors, its
native input intervals, and its case-(a) middle-time strip. The external
case-(b) norm is assigned to the distinguished linear core. All functions
are explicit and measurable; unused old labels have empty coordinate
fibers and contribute the identity.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Product of the original nonnegative norm factors belonging to one coarse core. -/
@[expose] noncomputable def sourceCoreRawNorm {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) : ℝ≥0∞ :=
  ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b},
    ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a.1 (sourceCoreOldTimes D b z a))

/-- The literal source coordinate box of one coarse core. -/
@[expose] def sourceCoreTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) (b : FactorIdx D.S) :
    Set (SourceCoreCoordinate D b → ℝ) :=
  Set.pi Set.univ (fun j => Icc (enlargedTimeLower D c h (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))
    (enlargedTimeUpper D c h (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩)))

/-- The actual case-(a) strips whose pairs lie inside a particular core. -/
@[expose] def sourceCoreOrdering {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b → ℝ) : Prop :=
  ∀ a : Σ i : Fin D.S.I, Fin (D.S.m i), caseAPair D a → sourceCoreGroup D (.inr (.inl a)) = b →
    |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inl ⟨a.1,0⟩)| ≤
      |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inr (.inl a))|

/-- The external momentum multiplier belongs only to the distinguished linear core. -/
@[expose] noncomputable def sourceCoreMultiplier {d : ℕ} (D : SumintDatum d) (r : Mom d) : FactorIdx D.S → ℝ≥0∞
  | .inl i => caseBMultiplier D r i
  | .inr _ => 1

/-- The concrete local nonnegative coarse source factor, including intervals and ordering. -/
@[expose] noncomputable def sourceCoreNormFactor {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) : ℝ≥0∞ :=
  (sourceCoreTimeBox D c h b ∩ {z | sourceCoreOrdering D b z}).indicator
    (fun z => sourceCoreMultiplier D r b*sourceCoreRawNorm D L γ δ η p ν r t b z) z

/-- Each core's native interval box is measurable. -/
theorem measurableSet_sourceCoreTimeBox {d : ℕ} (D : SumintDatum d) (c h : ℝ) (b : FactorIdx D.S) :
    MeasurableSet (sourceCoreTimeBox D c h b) :=
  MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Icc)

/-- Projecting the old local times from a coarse core is measurable. -/
theorem measurable_sourceCoreOldTimes {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) : Measurable (fun z => sourceCoreOldTimes D b z a) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun z : SourceCoreCoordinate D b → ℝ => z ⟨a,j⟩)
  exact measurable_pi_apply (⟨a,j⟩ : SourceCoreCoordinate D b)

/-- The product of actual old norm factors in a coarse core is measurable. -/
theorem measurable_sourceCoreRawNorm {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (b : FactorIdx D.S) : Measurable (sourceCoreRawNorm D L γ δ η p ν r t b) := by
  apply Finset.measurable_prod
  intro a _
  exact ((measurable_sourceTimeNormFactor D hL γ δ η p ν r t a.1).comp
    (measurable_sourceCoreOldTimes D b a)).ennreal_ofReal

/-- The actual local case-(a) strip predicates are measurable. -/
theorem measurableSet_sourceCoreOrdering {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    MeasurableSet {z | sourceCoreOrdering D b z} := by
  have hu (v : D.S.TVar) : Measurable (fun z => sourceCoreLocalInput D b z v) :=
    (measurable_pi_apply v).comp (measurable_sourceCoreLocalInput D b)
  rw [show {z | sourceCoreOrdering D b z} =
    ⋂ a : Σ i : Fin D.S.I, Fin (D.S.m i), {z | caseAPair D a → sourceCoreGroup D (.inr (.inl a)) = b →
      |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inl ⟨a.1,0⟩)| ≤
        |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inr (.inl a))|} by
      ext z; simp only [Set.mem_ofPred_eq,Set.mem_iInter,sourceCoreOrdering]]
  apply MeasurableSet.iInter
  intro a
  by_cases ha : caseAPair D a
  · by_cases hb : sourceCoreGroup D (.inr (.inl a)) = b
    · simp only [ha,hb,true_implies]
      have hl : Measurable (fun z : SourceCoreCoordinate D b → ℝ =>
          |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inl ⟨a.1,0⟩)|) := by
        fun_prop
      have hr : Measurable (fun z : SourceCoreCoordinate D b → ℝ =>
          |sourceCoreLocalInput D b z (.inl ⟨a.1,a.2.succ⟩)-sourceCoreLocalInput D b z (.inr (.inl a))|) := by
        fun_prop
      exact measurableSet_le hl hr
    · simp only [hb,ha,false_implies,true_implies,Set.ofPred_true,MeasurableSet.univ]
  · simp only [ha,false_implies,Set.ofPred_true,MeasurableSet.univ]

/-- Every concrete coarse source norm factor is measurable on its native local coordinates. -/
theorem measurable_sourceCoreNormFactor {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (b : FactorIdx D.S) : Measurable (sourceCoreNormFactor D L γ δ η p ν r t c h b) :=
  (measurable_const.mul (measurable_sourceCoreRawNorm D hL γ δ η p ν r t b)).indicator
    ((measurableSet_sourceCoreTimeBox D c h b).inter (measurableSet_sourceCoreOrdering D b))

end WaveTurbulence.Sumint

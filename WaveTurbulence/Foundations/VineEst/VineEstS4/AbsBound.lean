/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsMeas

/-! # Measurability and the box support of the CL-local summand (V5 Step 4b) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

section Dom
variable (R : CLRegionData G U a b) (layerFn : GBranch G.tree → ℕ) (t : Fin 3 → ℝ)

theorem measurable_parentClock_local (x : GNode G.tree) :
    Measurable (fun τ : CLInternalTime R => parentClock (t 0) (clLocalClock R t τ) x) :=
  measurable_parentClock _ _ (fun b => measurable_clLocalClock R t b) x

theorem measurableSet_localTimeDomain : MeasurableSet (clLocalTimeDomain R layerFn t) := by
  classical
  have hc := measurable_clLocalClock R t
  have hp := measurable_parentClock_local R t
  have hτ : ∀ v : ↥(clInteriorBranches R), Measurable fun τ : CLInternalTime R => τ v :=
    fun v => measurable_pi_apply v
  have hA : MeasurableSet {τ : CLInternalTime R | ∀ v : ↥(clInteriorBranches R), (layerFn v.1 : ℝ) < τ v ∧
      τ v < layerFn v.1 + 1 ∧ 0 < τ v ∧ τ v < parentClock (t 0) (clLocalClock R t τ) v.1.toNode} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun v => ?_
    rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_and]
    exact MeasurableSet.inter (measurableSet_lt measurable_const (hτ v)) (MeasurableSet.inter
      (measurableSet_lt (hτ v) measurable_const) (MeasurableSet.inter (measurableSet_lt measurable_const (hτ v))
      (measurableSet_lt (hτ v) (hp _))))
  have hP : ∀ (P : Prop) (j : Fin 3), MeasurableSet {τ : CLInternalTime R | P → t (j) < clLocalClock R t τ b} := by
    intro P j
    by_cases h : P
    · simp only [h, true_implies]
      exact measurableSet_lt measurable_const (hc b)
    · simp only [h, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  unfold clLocalTimeDomain
  rw [Set.ofPred_and, Set.ofPred_and]
  exact hA.inter ((hP _ 1).inter (hP _ 2))

/-- The time domain lies in the unit boxes of the layers. -/
theorem localTimeDomain_subset_box :
    clLocalTimeDomain R layerFn t ⊆
      Set.pi Set.univ fun v : ↥(clInteriorBranches R) => Set.Icc (layerFn v.1 : ℝ) (layerFn v.1 + 1) := by
  intro τ hτ v _
  have h := hτ.1 v
  exact ⟨h.1.le, h.2.1.le⟩

theorem volume_box :
    (volume : Measure (CLInternalTime R)) (Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
      Set.Icc (layerFn v.1 : ℝ) (layerFn v.1 + 1)) = 1 := by
  rw [volume_pi_pi]
  simp

end Dom

end WaveTurbulence.VineEstS4

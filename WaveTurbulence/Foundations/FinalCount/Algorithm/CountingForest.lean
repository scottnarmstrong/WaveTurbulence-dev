/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Problem
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ScanMode
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestGapReserve
import Mathlib.Tactic

/-! # An actual decorated forest with the source scan mode and gap reserve

The stored reserve equality is bookkeeping from the initial bond budget,
not an analytic estimate. No count bound or operation-count conclusion is
a field of this carrier.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}

inductive ForestScanMode (F : List (Problem.{u,v} V d L w c g))
  | globalScan : ForestScanMode F
  | ladder (p : Problem.{u,v} V d L w c g) (hp : p ∈ F) (head : LadderHead p.state) : ForestScanMode F
  | terminalComponent (p : Problem.{u,v} V d L w c g) (hp : p ∈ F)
      (noDouble : ¬HasDegreeThreePair p.state.graph 2) : ForestScanMode F

structure CountingForest (V : Type v) [DecidableEq V] (d : ℕ) (L γ η : ℝ)
    (w : Mom d) (c : ℝ) (B : ℕ) where
  gap : ℝ
  problems : List (Problem.{u,v} V d L w c gap)
  mode : ForestScanMode problems
  reserve_eq : gap = forestGapReserve B L γ η (problems.map Problem.state)

noncomputable def CountingForest.graphs {γ η : ℝ} {B : ℕ}
    (F : CountingForest.{u,v} V d L γ η w c B) : List (State.{u,v} V) := F.problems.map Problem.state

noncomputable def CountingForest.weight {γ η : ℝ} {B : ℕ}
    (F : CountingForest.{u,v} V d L γ η w c B) : ℕ := forestWeight F.graphs

noncomputable def CountingForest.value {γ η : ℝ} {B : ℕ}
    (F : CountingForest.{u,v} V d L γ η w c B) (δ C1 : ℝ) : ℝ≥0∞ :=
  (F.problems.map fun p => p.value γ δ C1).prod

noncomputable def CountingForest.singleton (γ η : ℝ)
    (p : Problem.{u,v} V d L w c (L^(-γ+η))) :
    CountingForest.{u,v} V d L γ η w c p.state.bondPotential where
  gap := L^(-γ+η)
  problems := [p]
  mode := .globalScan
  reserve_eq := by
    simp only [List.map_cons,List.map_nil,forestGapReserve,forestBonds,List.sum_cons,List.sum_nil,Nat.add_zero,
      sub_self,zero_mul,sub_zero]

theorem CountingForest.value_singleton (γ η : ℝ)
    (p : Problem.{u,v} V d L w c (L^(-γ+η))) (δ C1 : ℝ) :
    (CountingForest.singleton γ η p).value δ C1 = p.value γ δ C1 := by
  simp only [CountingForest.value,CountingForest.singleton,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

/-- The proved bond-budget lemma supplies the standing half-gap threshold
for every decorated forest, uniformly over its current graph carriers. -/
theorem CountingForest.half_gap_eventual (γ η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,∀ B : ℕ,(B : ℝ) ≤ 2*(1+Real.log L)^m →
      ∀ F : CountingForest.{u,v} V d L γ η w c B,L^(-γ+η)/2 ≤ F.gap := by
  filter_upwards [forestGapReserve_half_eventual (V := V) γ η hη m] with L hL B hB F
  rw [F.reserve_eq]
  exact hL B hB _

end WaveTurbulence.Mole.AppbAlgorithm

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchRoute
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceBranchCost
public import WaveTurbulence.Foundations.VineEst.VineEstS2.RouteProductBudget
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPredecessorBudget
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLTreeLabels

/-! # Exponential cost of the actual subtraction-only predecessor routes -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {tree : Fin w → TTree}

theorem signPredecessorRoute_charge (sig : Fin w → ℤˣ) (x : GBranch tree) :
    (Finset.univ.filter (fun v => x ∈ signPredecessorRoute sig v)).card ≤ 2 := by
  classical
  apply card_sourceSignInterval_starts_le_two sig x _
  intro v hv
  exact signPredecessorRoute_colorInterval sig v x (Finset.mem_filter.mp hv).2

/-- The actual constructed routes, without a route-charge hypothesis, have
total cost at most the square of the ordinary source branch-cost product. -/
theorem prod_signPredecessorRoute_cost (sig : Fin w → ℤˣ) :
    (∏ v : GBranch tree, ∏ u ∈ signPredecessorRoute sig v, branchPredecessorCost u) ≤
      (∏ u : GBranch tree, branchPredecessorCost u)^2 := by
  classical
  exact prod_route_cost_le_square (signPredecessorRoute sig) branchPredecessorCost
    branchPredecessorCost_pos (signPredecessorRoute_charge sig)

/-- Concrete universal coefficient budget after sign skipping on the actual
CL realization. The constant 6561 is independent of its shape and size. -/
theorem cl_signPredecessorRoute_cost_le {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    (∏ v : GBranch (CLTreeForest R),
      ∏ u ∈ signPredecessorRoute (fun _ : Fin 1 => G.sign a.toNode) v, branchPredecessorCost u) ≤
      6561^clLocalOrder1 R := by
  calc
    _ ≤ (∏ u : GBranch (CLTreeForest R), branchPredecessorCost u)^2 :=
      prod_signPredecessorRoute_cost _
    _ = (predecessorCostProduct (clRealizationTree R))^2 := by rw [prod_branchPredecessorCost]
    _ ≤ (81^clLocalOrder1 R)^2 := Nat.pow_le_pow_left (cl_predecessorCostProduct_le hU R) 2
    _ = 6561^clLocalOrder1 R := by rw [← pow_mul, Nat.mul_comm (clLocalOrder1 R) 2,pow_mul]; rfl

end WaveTurbulence.VineEstS2

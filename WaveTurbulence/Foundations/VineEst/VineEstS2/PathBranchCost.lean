/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.PositivePathCosts
public import WaveTurbulence.Foundations.VineEst.VineEstS2.PredecessorBudget

/-! # Literal finite branching product of local predecessor costs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- Leaf-count query for an optional subtree, extended by the trivial tree
at invalid addresses. Source cost statements use only valid branching nodes. -/
def optionLeafCount (T : Option TTree) : ℕ := leafCount (T.getD .leaf)

def pathBranchCost (T : TTree) (p : Path) : ℕ :=
  3*medianThree (optionLeafCount (Comb.subtree T (p++[0])))
    (optionLeafCount (Comb.subtree T (p++[1]))) (optionLeafCount (Comb.subtree T (p++[2])))

theorem pathBranchCost_zero (l m r : TTree) (p : Path) :
    pathBranchCost (.node l m r) (0::p) = pathBranchCost l p := by
  simp only [pathBranchCost,List.cons_append,Comb.subtree,ite_true,Fin.reduceEq]

theorem pathBranchCost_one (l m r : TTree) (p : Path) :
    pathBranchCost (.node l m r) (1::p) = pathBranchCost m p := by
  simp only [pathBranchCost,List.cons_append,Comb.subtree,ite_true,ite_false,Fin.reduceEq]

theorem pathBranchCost_two (l m r : TTree) (p : Path) :
    pathBranchCost (.node l m r) (2::p) = pathBranchCost r p := by
  simp only [pathBranchCost,List.cons_append,Comb.subtree,ite_false,Fin.reduceEq]

private theorem prod_pre (i : Fin 3) (S : Finset Path) (f : Path → ℕ) :
    (∏ p ∈ pre i S, f p) = ∏ p ∈ S, f (i::p) := by
  unfold pre
  rw [Finset.prod_image]
  intro p _ q _ hpq
  exact (List.cons.inj hpq).2

/-- The recursive DH21 numerical budget is exactly the finite product over
actual branching addresses, rather than an unrelated recurrence. -/
theorem prod_pathBranchCost (T : TTree) :
    (∏ p ∈ T.branching, pathBranchCost T p) = predecessorCostProduct T := by
  classical
  induction T with
  | leaf => simp only [branching,Finset.prod_empty,predecessorCostProduct]
  | node l m r hl hm hr =>
    rw [branching,Finset.prod_insert (by simp only [Finset.mem_union,nil_notMem_pre,false_or,not_false_eq_true])]
    have h01 := Comb.pre_disjoint (show (0:Fin 3) ≠ 1 by decide) l.branching m.branching
    have h02 := Comb.pre_disjoint (show (0:Fin 3) ≠ 2 by decide) l.branching r.branching
    have h12 := Comb.pre_disjoint (show (1:Fin 3) ≠ 2 by decide) m.branching r.branching
    rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨h02,h12⟩),Finset.prod_union h01]
    rw [prod_pre,prod_pre,prod_pre]
    simp_rw [pathBranchCost_zero,pathBranchCost_one,pathBranchCost_two]
    rw [hl,hm,hr]
    simp only [pathBranchCost,List.nil_append,Comb.subtree,Fin.reduceEq,ite_true,ite_false,
      optionLeafCount,Option.getD_some,predecessorCostProduct]

end WaveTurbulence.VineEstS2

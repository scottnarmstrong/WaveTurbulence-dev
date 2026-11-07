/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalDifferenceCoefficients

/-! # Opposite local source incidences have unit inverse coefficients -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Source-label relation used only by the local geometry helpers. -/
def HasUnitSourceDifference (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (u v : GNode (CLTreeForest R)) : Prop :=
  ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
    ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ z ∈ U, κ z.toNode = κ (z.child 0)-κ (z.child 1)+κ (z.child 2)) →
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
      κ (clTreeNode R u)-κ (clTreeNode R v) = ∑ o, σ o • clOriginValue hU R hG κ o

theorem HasUnitSourceDifference.symm (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) {u v : GNode (CLTreeForest R)}
    (h : HasUnitSourceDifference hU R hG u v) : HasUnitSourceDifference hU R hG v u := by
  obtain ⟨σ,hσ,he⟩ := h
  refine ⟨fun o => -σ o,?_,?_⟩
  · intro o
    rcases hσ o with h | h | h <;> simp only [h,IsUnitCoeff] <;> norm_num
  · intro E _ κ hc hp
    have hh := congrArg (fun x : E => -x) (he κ hc hp)
    simpa only [neg_sub,Finset.sum_neg_distrib,neg_smul] using hh

/-- Parent,left,middle,right incidence parity, after removing the common
node sign. -/
def treeSlotParity (i : Fin 4) : ℤ := if i = 0 ∨ i = 2 then 1 else -1

def treeSlotNode {w : ℕ} {tree : Fin w → TTree} (q : GBranch tree) : Fin 4 → GNode tree :=
  Fin.cases q.toNode q.child

private theorem child_leaf_disjoint {w : ℕ} {tree : Fin w → TTree} (q : GBranch tree)
    (i j : Fin 3) (hij : i ≠ j) : Disjoint (q.child i).leavesBelow (q.child j).leavesBelow := by
  apply Finset.disjoint_left.mpr
  intro ℓ hi hj
  exact hij (q.eq_of_isDesc_child (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

/-- The eight possible ordered opposite-incidence pairs exhaust the local
cases. Thus all such coordinate differences have a unit source inverse row. -/
theorem clTreeSlot_difference_coeffs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (q : GBranch (CLTreeForest R)) (i j : Fin 4)
    (h : treeSlotParity i = -treeSlotParity j) :
    HasUnitSourceDifference hU R hG (treeSlotNode q i) (treeSlotNode q j) := by
  have hs := nodeSign_child (fun _ : Fin 1 => G.sign a.toNode) q
  have h01 : HasUnitSourceDifference hU R hG q.toNode (q.child 0) :=
    clDescendant_difference_coeffs hU R hG q _ _ (q.isDesc_child 0) hs.1.symm
  have h03 : HasUnitSourceDifference hU R hG q.toNode (q.child 2) :=
    clDescendant_difference_coeffs hU R hG q _ _ (q.isDesc_child 2) hs.2.2.symm
  have h12 : HasUnitSourceDifference hU R hG (q.child 0) (q.child 1) :=
    clDisjoint_difference_coeffs hU R hG q _ _ (child_leaf_disjoint q 0 1 (by decide)) (hs.2.1.trans (congrArg Neg.neg hs.1.symm))
  have h23 : HasUnitSourceDifference hU R hG (q.child 1) (q.child 2) :=
    clDisjoint_difference_coeffs hU R hG q _ _ (child_leaf_disjoint q 1 2 (by decide)) (by rw [hs.2.1,hs.2.2,neg_neg])
  fin_cases i <;> fin_cases j <;> norm_num [treeSlotParity] at h
  all_goals first
    | exact h01
    | exact h03
    | exact h12
    | exact h23
    | exact HasUnitSourceDifference.symm hU R hG h01
    | exact HasUnitSourceDifference.symm hU R hG h03
    | exact HasUnitSourceDifference.symm hU R hG h12
    | exact HasUnitSourceDifference.symm hU R hG h23

end WaveTurbulence.VineEstS2

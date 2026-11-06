/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamDirectedTransport
import Mathlib.Tactic

/-! # Source momentum across a cap is zero or the signed joint gap

The cut identity follows by summing actual directed incidence rows; it is
independent of orientations and of any choice of coordinates.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [AddCommGroup E]

/-- The outgoing-minus-incoming crossing sign of an actual directed bond. -/
@[expose] def cutSign (ends : β → V×V) (C : Finset V) (j : β) : ℤ :=
  (if (ends j).1 ∈ C then 1 else 0)-(if (ends j).2 ∈ C then 1 else 0)

omit [Fintype β] [AddCommGroup E] in
/-- Incidence signs telescope to the two endpoint membership indicators. -/
theorem sum_vertex_incidence (ends : β → V×V) (C : Finset V) (j : β) :
    (∑ v ∈ C,-energySign ends v j)=cutSign ends C j := by
  simp [energySign,cutSign,neg_sub,Finset.sum_sub_distrib,eq_comm]

/-- Summing conservation over a cap leaves exactly its physical cut flow. -/
theorem sum_directedFlow_cut (ends : β → V×V) (C : Finset V) (k : β → E) :
    (∑ v ∈ C,directedFlow ends v k)=∑ j,cutSign ends C j • k j := by
  simp only [directedFlow]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _hj
  rw [← sum_smul,sum_vertex_incidence]

/-- If every nonjoint atom conserves momentum, the cap flow is determined
only by its joint memberships and the two actual joint divergences. -/
theorem cap_flow_from_joints (ends : β → V×V) (C : Finset V) (k : β → E)
    (a b : V) (hab : a ≠ b)
    (hzero : ∀ v ∈ C,v ≠ a → v ≠ b → directedFlow ends v k=0) :
    (∑ j,cutSign ends C j • k j)=
      (if a ∈ C then directedFlow ends a k else 0)+
        (if b ∈ C then directedFlow ends b k else 0) := by
  rw [← sum_directedFlow_cut]
  have hs : ∑ v ∈ C,directedFlow ends v k=
      ∑ v ∈ C ∩ {a,b},directedFlow ends v k := by
    symm
    apply sum_subset inter_subset_left
    intro v hv hnot
    have hn : v ≠ a ∧ v ≠ b := by
      simpa only [mem_inter,hv,true_and,mem_insert,mem_singleton,not_or] using hnot
    exact hzero v hv hn.1 hn.2
  rw [hs,inter_comm,← filter_mem_eq_inter,sum_filter]
  rw [sum_pair hab]

/-- A cap's physical cut gap is zero or a signed copy of the root gap.
The sign depends only on which joint is contained in the cap. -/
theorem cap_flow_gap (ends : β → V×V) (C : Finset V) (k : β → E)
    (a b : V) (hab : a ≠ b) (r : E)
    (ha : directedFlow ends a k=r) (hb : directedFlow ends b k= -r)
    (hzero : ∀ v ∈ C,v ≠ a → v ≠ b → directedFlow ends v k=0) :
    (∑ j,cutSign ends C j • k j)=
      ((if a ∈ C then (1 : ℤ) else 0)-(if b ∈ C then (1 : ℤ) else 0)) • r := by
  rw [cap_flow_from_joints ends C k a b hab hzero,ha,hb]
  by_cases hca : a ∈ C <;> by_cases hcb : b ∈ C <;>
    simp only [hca,hcb,ite_true,ite_false,sub_self,zero_zsmul,one_zsmul,
      zero_sub,neg_one_zsmul,add_neg_cancel,add_zero,zero_add,sub_zero]

end WaveTurbulence.Vine.Param

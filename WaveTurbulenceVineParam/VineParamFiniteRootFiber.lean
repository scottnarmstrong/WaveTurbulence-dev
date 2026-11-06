/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphContractFiber
import Mathlib.Tactic

/-! # Finite source joint conservation and exchange of the included joint -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [AddCommGroup E]

/-- Interchanging the joint designations negates the physical root gap. -/
theorem rootForcing_swap (a b : V) (hab : a ≠ b) (r : E) (v : V) :
    rootForcing a b r v=rootForcing b a (-r) v := by
  by_cases hva : v=a
  · subst v
    simp [rootForcing,hab]
  · by_cases hvb : v=b
    · subst v
      simp [rootForcing,Ne.symm hab]
    · simp [rootForcing,hva,hvb]

/-- The source fiber for the opposite included joint has the same actual
labels and the opposite gap. This introduces no symmetry of the template. -/
@[expose] def rootFiberSwap (ends : β → V×V) (a b : V) (hab : a ≠ b) (r : E) :
    DirectedRootFiber ends a b r ≃ DirectedRootFiber ends b a (-r) :=
  Equiv.subtypeEquivRight (fun k => by simp only [HasRootFlow,rootForcing_swap a b hab r])

/-- All internal directed incidences cancel on the whole finite atom set. -/
theorem sum_directedFlow_univ [Fintype V] (ends : β → V×V) (k : β → E) :
    (∑ v,directedFlow ends v k)=0 := by
  rw [sum_directedFlow_cut ends univ k]
  simp only [cutSign,mem_univ,ite_true,sub_self,zero_zsmul,sum_const_zero]

/-- The second joint conservation row is forced by every interior row. -/
theorem second_joint_flow_neg_finite [Fintype V] (ends : β → V×V) (k : β → E)
    (a b : V) (hab : a ≠ b)
    (hz : ∀ v,v ≠ a → v ≠ b → directedFlow ends v k=0) :
    directedFlow ends b k= -directedFlow ends a k := by
  have h := cap_flow_from_joints ends univ k a b hab (fun v _ => hz v)
  simp only [cutSign,mem_univ,ite_true,sub_self,zero_zsmul,sum_const_zero] at h
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact h.symm

end WaveTurbulence.Vine.Param

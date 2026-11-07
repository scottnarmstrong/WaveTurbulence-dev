/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairFigure
import Mathlib.Tactic

/-! # Rule two's distinct-neighbor profiles with a shared boundary atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SinglePairEdges
variable {M : Molecule V D} {a b : V}

theorem figure_of_shared_boundary (data : SinglePairEdges M a b)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3)
    (hl : data.left.neighbor 0 ≠ data.left.neighbor 1)
    (hr : data.right.neighbor 0 ≠ data.right.neighbor 1)
    (hshare : data.left.neighbor 0 = data.right.neighbor 0) : SinglePairFigure M := by
  classical
  let c := data.left.neighbor 0
  let d := data.left.neighbor 1
  let p := data.right.neighbor 1
  have hc : c ∈ M.atoms := data.left.neighbor_mem 0
  have hd : d ∈ M.atoms := data.left.neighbor_mem 1
  have hp : p ∈ M.atoms := data.right.neighbor_mem 1
  have hca : c ≠ a := data.left.neighbor_ne_center 0
  have hcb : c ≠ b := data.left.neighbor_ne_partner 0
  have hda' : d ≠ a := data.left.neighbor_ne_center 1
  have hdb' : d ≠ b := data.left.neighbor_ne_partner 1
  have hpa : p ≠ a := data.right.neighbor_ne_partner 1
  have hpb : p ≠ b := data.right.neighbor_ne_center 1
  have hcd : c ≠ d := hl
  have hcp : c ≠ p := fun h => hr (hshare.symm.trans h)
  by_cases hdp : d = p
  · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
    have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    let r := s33new2Realization M hab hnd hm hda hdb data rfl rfl hshare.symm hdp.symm
    exact ⟨.s33new2,by simp,⟨r⟩⟩
  · have hnd : ([a,b,c,d,p] : List V).Nodup := by simp_all [ne_comm]
    have hm : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
    let r := s33new1Realization M hab hnd hm hda hdb data rfl rfl hshare.symm rfl
    exact ⟨.s33new1,by simp,⟨r⟩⟩

end SinglePairEdges
end WaveTurbulence.Mole.AppbAlgorithm

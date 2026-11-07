/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairFigure
import Mathlib.Tactic

/-! # Rule two's profiles when two boundary bonds have the same neighbor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace SinglePairEdges
variable {M : Molecule V D} {a b : V}

theorem figure_of_left_double (data : SinglePairEdges M a b)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3)
    (hl : data.left.neighbor 0 = data.left.neighbor 1) : SinglePairFigure M := by
  classical
  let c := data.left.neighbor 0
  let d := data.right.neighbor 0
  let p := data.right.neighbor 1
  have hc : c ∈ M.atoms := data.left.neighbor_mem 0
  have hd : d ∈ M.atoms := data.right.neighbor_mem 0
  have hp : p ∈ M.atoms := data.right.neighbor_mem 1
  have hca : c ≠ a := data.left.neighbor_ne_center 0
  have hcb : c ≠ b := data.left.neighbor_ne_partner 0
  have hda' : d ≠ a := data.right.neighbor_ne_partner 0
  have hdb' : d ≠ b := data.right.neighbor_ne_center 0
  have hpa : p ≠ a := data.right.neighbor_ne_partner 1
  have hpb : p ≠ b := data.right.neighbor_ne_center 1
  by_cases hr : d = p
  · by_cases hcd : c = d
    · have hnd : ([a,b,c] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      let r := s33new4Realization M hab hnd hm hda hdb data rfl hl.symm hcd.symm (hr.symm.trans hcd.symm)
      exact ⟨.s33new4,by simp,⟨r⟩⟩
    · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := s33new3Realization M hab hnd hm hda hdb data rfl hl.symm rfl hr.symm
      exact ⟨.s33new3,by simp,⟨r⟩⟩
  · by_cases hcd : c = d
    · have hnd : ([a,b,c,p] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,p] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := s33new6Realization M hab hnd hm hda hdb data rfl hl.symm hcd.symm rfl
      exact ⟨.s33new6,by simp,⟨r⟩⟩
    · by_cases hcp : c = p
      · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> assumption
        let data' := data.reindex (Equiv.refl _) (Equiv.swap 0 1)
        let r := s33new6Realization M hab hnd hm hda hdb data' (by rfl) (by exact hl.symm)
          (by simpa [data',reindex,p] using hcp.symm) (by simp [data',reindex,d])
        exact ⟨.s33new6,by simp,⟨r⟩⟩
      · have hnd : ([a,b,c,d,p] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
        let r := s33new5Realization M hab hnd hm hda hdb data rfl hl.symm rfl rfl
        exact ⟨.s33new5,by simp,⟨r⟩⟩

end SinglePairEdges
end WaveTurbulence.Mole.AppbAlgorithm

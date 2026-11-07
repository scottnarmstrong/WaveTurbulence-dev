/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.MixedPairPatterns
import Mathlib.Tactic

/-! # The four source double-bonded degree-three/four profiles are exhaustive -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def D34Figure (M : Molecule V D) : Prop :=
  ∃ k ∈ ([AppbPatternKind.d34one,.d34two,.d34three,.d34four] : List _),
    Nonempty (AppbRealization M k.pattern)

namespace MixedPairEdges
variable {M : Molecule V D} {a b : V}

theorem d34_figure (data : MixedPairEdges M a b 2 1 2)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) : D34Figure M := by
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
      let r := d34fourRealization M hab hnd hm hda hdb data rfl hcd.symm (hr.symm.trans hcd.symm)
      exact ⟨.d34four,by simp,⟨r⟩⟩
    · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := d34threeRealization M hab hnd hm hda hdb data rfl rfl hr.symm
      exact ⟨.d34three,by simp,⟨r⟩⟩
  · by_cases hcd : c = d
    · have hnd : ([a,b,c,p] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,p] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := d34twoRealization M hab hnd hm hda hdb data rfl hcd.symm rfl
      exact ⟨.d34two,by simp,⟨r⟩⟩
    · by_cases hcp : c = p
      · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> assumption
        let data' := data.reindex (Equiv.refl _) (Equiv.swap 0 1)
        let r := d34twoRealization M hab hnd hm hda hdb data' (by rfl)
          (by simpa [data',reindex,p] using hcp.symm) (by simp [data',reindex,d])
        exact ⟨.d34two,by simp,⟨r⟩⟩
      · have hnd : ([a,b,c,d,p] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
        let r := d34oneRealization M hab hnd hm hda hdb data rfl rfl rfl
        exact ⟨.d34one,by simp,⟨r⟩⟩

end MixedPairEdges

/-- DH23 Appendix B rule four's figure-existence assertion. -/
theorem exists_d34_figure (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (hm : M.bondsBetween a b = 2) :
    D34Figure M :=
  (mixedPairEdges M hno hda hdb hm).d34_figure ha hb hab hda hdb

end WaveTurbulence.Mole.AppbAlgorithm

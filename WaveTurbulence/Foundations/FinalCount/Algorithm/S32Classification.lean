/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.MixedPairPatterns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundaryPairCount
import Mathlib.Tactic

/-! # Exhaustive degree-three/two profiles after the bridge stage -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def S32Figure (M : Molecule V D) : Prop :=
  ∃ k ∈ ([AppbPatternKind.s32one,.s32two,.s32three,.s32four] : List _),
    Nonempty (AppbRealization M k.pattern)

namespace MixedPairEdges
variable {M : Molecule V D} {a b : V}

theorem s32_figure (data : MixedPairEdges M a b 1 2 1)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) : S32Figure M := by
  classical
  let c := data.left.neighbor 0
  let d := data.left.neighbor 1
  let p := data.right.neighbor 0
  have hc : c ∈ M.atoms := data.left.neighbor_mem 0
  have hd : d ∈ M.atoms := data.left.neighbor_mem 1
  have hp : p ∈ M.atoms := data.right.neighbor_mem 0
  have hca : c ≠ a := data.left.neighbor_ne_center 0
  have hcb : c ≠ b := data.left.neighbor_ne_partner 0
  have hda' : d ≠ a := data.left.neighbor_ne_center 1
  have hdb' : d ≠ b := data.left.neighbor_ne_partner 1
  have hpa : p ≠ a := data.right.neighbor_ne_partner 0
  have hpb : p ≠ b := data.right.neighbor_ne_center 0
  by_cases hl : c = d
  · by_cases hcp : c = p
    · have hnd : ([a,b,c] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      let r := s32twoRealization M hab hnd hm hda hdb data rfl hl.symm hcp.symm
      exact ⟨.s32two,by simp,⟨r⟩⟩
    · have hnd : ([a,b,c,p] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,p] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := s32oneRealization M hab hnd hm hda hdb data rfl hl.symm rfl
      exact ⟨.s32one,by simp,⟨r⟩⟩
  · by_cases hdp : d = p
    · have hnd : ([a,b,c,d] : List V).Nodup := by simp_all [ne_comm]
      have hm : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms := by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      let r := s32fourRealization M hab hnd hm hda hdb data rfl rfl hdp.symm
      exact ⟨.s32four,by simp,⟨r⟩⟩
    · by_cases hcp : c = p
      · have hnd : ([a,b,d,c] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,d,c] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> assumption
        let data' := data.reindex (Equiv.swap 0 1) (Equiv.refl _)
        let r := s32fourRealization M hab hnd hm hda hdb data'
          (by simp [data',reindex,d]) (by simp [data',reindex,c]) (by exact hcp.symm)
        exact ⟨.s32four,by simp,⟨r⟩⟩
      · have hnd : ([a,b,c,d,p] : List V).Nodup := by simp_all [ne_comm]
        have hm : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms := by
          intro v hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
        let r := s32threeRealization M hab hnd hm hda hdb data rfl rfl rfl
        exact ⟨.s32three,by simp,⟨r⟩⟩

end MixedPairEdges

/-- DH23 Appendix B rule five. The earlier bridge stage forces the
positive multiplicity to be one before the four figures are enumerated. -/
theorem exists_s32_figure (M : Molecule V D) (hno : AppbNoLoops M)
    (hnt : AppbNoTripleBonds M) (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) (hm : 0 < M.bondsBetween a b) :
    S32Figure M := by
  have hcap := hnt a ha b hb hab
  have hn : M.bondsBetween a b ≠ 2 := by
    intro hh
    obtain ⟨e,he⟩ := exists_bridge_of_three_two_double M hno hab hda hdb hh
    exact hbridge e he
  have hsingle : M.bondsBetween a b = 1 := by omega
  exact (mixedPairEdges M hno hda hdb hsingle).s32_figure ha hb hab hda hdb

end WaveTurbulence.Mole.AppbAlgorithm

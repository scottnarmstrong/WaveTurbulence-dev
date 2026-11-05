/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockChains
public import WaveTurbulence.Foundations.Molecule.MoleculeSingleDeficit
import Mathlib.Tactic

/-! # Parent flow through consecutive CL ingredients
TARGET `blockchainprop`: a shared joint has exactly one internal parent
among its adjacent ingredients, and an endpoint's parent is unchanged
when its actual internal degree is unchanged in the whole block.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem internalParent_mono {A B : Finset (GBranch G.tree)} (hAB : A ⊆ B) {v : GBranch G.tree} :
    InternalParent G A v → InternalParent G B v := by
  rintro ⟨hn,hp⟩
  exact ⟨hn,hAB hp⟩

theorem internalParent_eq_of_degree_eq {A B : Finset (GBranch G.tree)}
    (hAB : A ⊆ B) {v : GBranch G.tree} (hv : v ∈ A)
    (hd : G.molecule.degIn A v = G.molecule.degIn B v) :
    InternalParent G A v ↔ InternalParent G B v := by
  constructor
  · exact internalParent_mono G hAB
  · rintro ⟨hn,hp⟩
    let x : GardenDart G := .inl (⟨v,hn⟩,false)
    have hmem : x ∈ (G.molecule.dartsAt v).filter (G.molecule.InGroup B) :=
      mem_filter.mpr ⟨(mem_dartsAt G.molecule v x).mpr rfl,hAB hv,hp⟩
    rw [← internal_darts_eq_of_degree_eq G.molecule hAB v hd] at hmem
    exact ⟨hn,(mem_filter.mp hmem).2.2⟩

theorem segment_shared_parent_exclusion {A B : GardenBlockSegment G}
    (hf : SegmentFollows G A B) :
    ¬ (InternalParent G A.atoms A.rightJoint ∧ InternalParent G B.atoms B.leftJoint) := by
  rintro ⟨ha,hb⟩
  have hb' : InternalParent G B.atoms A.rightJoint := hf.1.symm ▸ hb
  obtain ⟨hn,hpa⟩ := ha
  obtain ⟨hn',hpb⟩ := hb'
  have hp : GNode.parent A.rightJoint.toNode hn ∈ A.atoms ∩ B.atoms := mem_inter.mpr ⟨hpa,hpb⟩
  rw [hf.2] at hp
  have he := congrArg (fun v : GBranch G.tree => v.1.2.length) (mem_singleton.mp hp)
  change A.rightJoint.1.2.dropLast.length = A.rightJoint.1.2.length at he
  rw [List.length_dropLast] at he
  have hpos := List.length_pos_of_ne_nil hn
  omega

private theorem left_flow_logic {L R N : Prop} (h1 : L ∨ R) (h2 : ¬ (L ∧ R))
    (h3 : R ∨ N) (h4 : ¬ (R ∧ N)) : L ↔ N := by tauto

theorem segment_left_parent_transfer {A B : GardenBlockSegment G}
    (hf : SegmentFollows G A B)
    (hCL : CLParentPattern G A.atoms A.leftJoint A.rightJoint ∨
      CLParentPattern G A.atoms A.rightJoint A.leftJoint) :
    InternalParent G A.atoms A.leftJoint ↔ InternalParent G B.atoms B.leftJoint := by
  have h1 : InternalParent G A.atoms A.leftJoint ∨ InternalParent G A.atoms A.rightJoint :=
    hCL.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have h2 : ¬ (InternalParent G A.atoms A.leftJoint ∧ InternalParent G A.atoms A.rightJoint) :=
    fun h => segment_parent_exclusion G A h.1 h.2
  exact left_flow_logic h1 h2 (segment_shared_parent G hf) (segment_shared_parent_exclusion G hf)

/-- All-CL chains propagate the same left-parent flag through every ingredient. -/
theorem chain_all_cl_left_constant (A : GardenBlockSegment G) (rest : List (GardenBlockSegment G))
    (hc : (A :: rest).IsChain (SegmentFollows G))
    (hCL : ∀ B ∈ A :: rest, CLParentPattern G B.atoms B.leftJoint B.rightJoint ∨
      CLParentPattern G B.atoms B.rightJoint B.leftJoint) :
    ∀ B ∈ A :: rest, InternalParent G A.atoms A.leftJoint ↔ InternalParent G B.atoms B.leftJoint := by
  intro B hB
  rcases List.mem_cons.mp hB with he | ht
  · subst B
    rfl
  · cases rest with
    | nil => exact (List.not_mem_nil ht).elim
    | cons C tail =>
      obtain ⟨hf,hrest⟩ := List.isChain_cons_cons.mp hc
      have hAC := segment_left_parent_transfer G hf (hCL A List.mem_cons_self)
      have htail : ∀ B ∈ C :: tail, CLParentPattern G B.atoms B.leftJoint B.rightJoint ∨
          CLParentPattern G B.atoms B.rightJoint B.leftJoint :=
        fun B hB => hCL B (List.mem_cons_of_mem _ hB)
      exact hAC.trans (chain_all_cl_left_constant C tail hrest htail B ht)
termination_by rest.length

/-- TARGET `blockchainprop`, all-CL assertion. The whole block's endpoint
degree two forces the same actual endpoint incidences as its end ingredients.
The inclusion premises express the source's concatenation containment. -/
theorem chain_all_cl_parent_pattern (A : GardenBlockSegment G) (rest : List (GardenBlockSegment G))
    (whole : Finset (GBranch G.tree))
    (hc : (A :: rest).IsChain (SegmentFollows G))
    (hCL : ∀ B ∈ A :: rest, CLParentPattern G B.atoms B.leftJoint B.rightJoint ∨
      CLParentPattern G B.atoms B.rightJoint B.leftJoint)
    (hsub : ∀ B ∈ A :: rest, B.atoms ⊆ whole)
    (hwhole : G.molecule.IsBlock whole A.leftJoint
      ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint) :
    CLParentPattern G whole A.leftJoint ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint ∨
    CLParentPattern G whole ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint A.leftJoint := by
  let last := (A :: rest).getLast (List.cons_ne_nil _ _)
  have hl : last ∈ A :: rest := List.getLast_mem _
  have hleft := internalParent_eq_of_degree_eq G (hsub A List.mem_cons_self) A.block.2.1
    ((block_joint_degrees G.molecule A.block).1.trans (block_joint_degrees G.molecule hwhole).1.symm)
  have hright := internalParent_eq_of_degree_eq G (hsub last hl) last.block.2.2.1
    ((block_joint_degrees G.molecule last.block).2.trans (block_joint_degrees G.molecule hwhole).2.symm)
  have hflow := chain_all_cl_left_constant G A rest hc hCL last hl
  rcases hCL last hl with h | h
  · left
    exact ⟨fun hp => h.1 (hflow.mp (hleft.mpr hp)),hright.mp h.2⟩
  · right
    exact ⟨fun hp => h.1 (hright.mpr hp),hleft.mp (hflow.mpr h.2)⟩

end WaveTurbulence.Mole

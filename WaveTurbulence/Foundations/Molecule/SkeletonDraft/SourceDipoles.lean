/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePortBonds
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LabelledGraph

/-! # Every source graph dipole uses two actual branching nodes

The ordered parent ports prevent a two-node parent cycle. Consequently one
of the two free attachment ports is a parent port, the key reduction to the
finite A/B mini table.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Three exact bonds between the ordered ports of two actual source branches. -/
structure BranchDipole {w : ℕ} (G : Garden w) where
  u : GBranch G.tree
  v : GBranch G.tree
  ne : u ≠ v
  perm : Equiv.Perm (Fin 4)
  free : Fin 4
  internal : ∀ i, i ≠ free → portMate G (.inr (u,i)) = .inr (v,perm i)

/-- All-active vertices of an ordinary garden's graph are actual branch labels. -/
theorem LabelledGarden.branch_of_active_vertex {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : G.garden.IsPlain) (v : Fin w ⊕ B) (ha : ∀ i, G.graph.mate (v,i) ≠ (v,i)) :
    ∃ b : GBranch G.garden.tree, v = .inr (G.label b) := by
  cases v with
  | inl j => exact (ha 1 (G.graph_root_inactive j 1 (by decide))).elim
  | inr b =>
    obtain ⟨c,hc⟩ := (G.graph_active_vertex_iff hG b).mp ha
    exact ⟨c,congrArg Sum.inr hc.symm⟩

/-- A labelled graph redex gives three literal source bonds, with no assumed mini characterization. -/
theorem LabelledGarden.branchDipole_of_graph {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : G.garden.IsPlain) (D : Dipole G.graph.mate) :
    ∃ E : BranchDipole G.garden, D.u = .inr (G.label E.u) ∧ D.v = .inr (G.label E.v) ∧
      E.perm = D.perm ∧ E.free = D.free := by
  obtain ⟨b,hb⟩ := G.branch_of_active_vertex hG D.u D.active_u
  obtain ⟨c,hc⟩ := G.branch_of_active_vertex hG D.v D.active_v
  have hn : b ≠ c := by
    intro he
    subst c
    exact D.ne (hb.trans hc.symm)
  let E : BranchDipole G.garden := {
    u := b
    v := c
    ne := hn
    perm := D.perm
    free := D.free
    internal := fun i hi => by
      have he := D.internal i hi
      rw [hb,hc] at he
      exact G.portEmbedding.injective ((G.graph_mate_embedding (.inr (b,i))).symm.trans he) }
  exact ⟨E,hb,hc,rfl,rfl⟩

namespace BranchDipole

/-- Read the same source mini piece from the other branching node. -/
def flip {w : ℕ} {G : Garden w} (D : BranchDipole G) : BranchDipole G where
  u := D.v
  v := D.u
  ne := D.ne.symm
  perm := D.perm.symm
  free := D.perm D.free
  internal j hj := by
    let i := D.perm.symm j
    have hi : i ≠ D.free := fun h => hj
      ((D.perm.apply_symm_apply j).symm.trans (congrArg D.perm h))
    have he := D.internal i hi
    have hh := portMate_involutive G (.inr (D.u,i))
    rw [he] at hh
    simpa only [i,Equiv.apply_symm_apply] using hh

/-- A source dipole has a free parent port at at least one endpoint. Otherwise
its two internal parent bonds would make each branch a child of the other. -/
theorem free_parent {w : ℕ} {G : Garden w} (D : BranchDipole G) : D.free = 0 ∨ D.perm D.free = 0 := by
  by_cases hf : D.free = 0
  · exact Or.inl hf
  by_cases hp : D.perm D.free = 0
  · exact Or.inr hp
  have h0 := D.internal 0 (Ne.symm hf)
  have hp0 : D.perm 0 ≠ 0 := by
    intro he
    rw [he] at h0
    exact portMate_parent_ne_parent G D.u D.v h0
  obtain ⟨i,hi⟩ := Fin.exists_succ_eq_of_ne_zero hp0
  have hu : D.u.toNode = D.v.child i := (portMate_parent_child_iff G D.u D.v i).mp (by rw [hi]; exact h0)
  let j := D.perm.symm 0
  have hpj : D.perm j = 0 := D.perm.apply_symm_apply 0
  have hj : j ≠ D.free := fun he => hp ((congrArg D.perm he).symm.trans hpj)
  have hj0 : j ≠ 0 := fun he => hp0 ((congrArg D.perm he).symm.trans hpj)
  have h1 := D.internal j hj
  rw [hpj] at h1
  obtain ⟨k,hk⟩ := Fin.exists_succ_eq_of_ne_zero hj0
  have hv : D.u.child k = D.v.toNode := (portMate_child_parent_iff G D.u D.v k).mp (by rw [hk]; exact h1)
  exact (not_mutual_children G D.u D.v i k ⟨hu,hv.symm⟩).elim

end BranchDipole
end WaveTurbulence.Reg.Skeleton

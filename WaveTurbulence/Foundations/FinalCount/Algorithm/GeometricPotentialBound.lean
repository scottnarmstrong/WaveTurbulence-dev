/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActiveEditBounds
import Mathlib.Tactic

/-! # Every non-ladder graph edit has a universal bounded potential decrease -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

theorem GeometricStep.activePotential_drop_le {s t : State.{u,v} V} (h : GeometricStep s t)
    (hM : s.graph.IsMolecule) (hN : t.graph.IsMolecule) :
    activeLinkPotential s.graph-20 ≤ activeLinkPotential t.graph := by
  cases h with
  | bridge e =>
    have hh := bond_removal_activePotential_drop_le s.graph hM e
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential (eraseBond s.graph e)
    omega
  | delete k r =>
    have hh := deletion_activePotential_drop_le r
    have hcard : k.pattern.removed.card ≤ 4 ∧ k.pattern.vertices.card ≤ 6 := by cases k <;> decide
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential r.post
    omega
  | common r =>
    have hh := deletion_activePotential_drop_le r
    have hcard : appbR23Common.removed.card = 3 ∧ appbR23Common.vertices.card = 4 := by decide
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential r.post
    omega
  | reinsertS33 r =>
    have hdel := deletion_activePotential_drop_le r
    have hcard : AppbPatternKind.s33.pattern.removed.card = 2 ∧ AppbPatternKind.s33.pattern.vertices.card = 6 := by decide
    have hadd : activeLinkPotential r.post-8 ≤ activeLinkPotential (r.directedPostWithBond 3 5 ⟨1,by decide⟩) := by
      change (r.directedPostWithBond 3 5 ⟨1,by decide⟩).IsMolecule at hN
      unfold AppbRealization.directedPostWithBond at hN ⊢
      split_ifs at hN ⊢
      · exact insertion_activePotential_drop_le r.post _ _
          (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 5 (by decide) (by decide)) hN
      · exact insertion_activePotential_drop_le r.post _ _
          (r.vertex_mem_post 5 (by decide) (by decide)) (r.vertex_mem_post 3 (by decide) (by decide)) hN
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential (r.directedPostWithBond 3 5 ⟨1,by decide⟩)
    omega
  | reinsertD33 r =>
    have hdel := deletion_activePotential_drop_le r
    have hcard : AppbPatternKind.d33.pattern.removed.card = 2 ∧ AppbPatternKind.d33.pattern.vertices.card = 4 := by decide
    have hadd : activeLinkPotential r.post-8 ≤ activeLinkPotential (r.directedPostWithBond 3 4 ⟨2,by decide⟩) := by
      change (r.directedPostWithBond 3 4 ⟨2,by decide⟩).IsMolecule at hN
      unfold AppbRealization.directedPostWithBond at hN ⊢
      split_ifs at hN ⊢
      · exact insertion_activePotential_drop_le r.post _ _
          (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide)) hN
      · exact insertion_activePotential_drop_le r.post _ _
          (r.vertex_mem_post 4 (by decide) (by decide)) (r.vertex_mem_post 3 (by decide) (by decide)) hN
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential (r.directedPostWithBond 3 4 ⟨2,by decide⟩)
    omega
  | r32 r z =>
    have h1 := deletion_activePotential_drop_le r
    have h2 := deletion_activePotential_drop_le z
    have hc1 : AppbPatternKind.r3.pattern.removed.card = 1 ∧ AppbPatternKind.r3.pattern.vertices.card = 4 := by decide
    have hc2 : AppbPatternKind.s33new3.pattern.removed.card = 2 ∧ AppbPatternKind.s33new3.pattern.vertices.card = 4 := by decide
    change activeLinkPotential s.graph-20 ≤ activeLinkPotential z.post
    omega

end WaveTurbulence.Mole.AppbAlgorithm

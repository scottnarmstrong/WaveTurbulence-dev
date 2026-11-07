/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.State
public import WaveTurbulence.Foundations.FinalCount.AppBBondErasure
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBR3CombinedEffects
import Mathlib.Tactic

/-! # A geometric envelope containing the actual Appendix B rewrites

This relation is deliberately not the source algorithm: it imposes neither
operation priorities nor label tests. It records actual graph rewrites so
that their common termination argument can be proved once. Source-selected
steps will supply their own graph and decoration premises.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive GeometricStep : State.{u,v} V → State.{u,v} V → Prop
  | bridge (s : State.{u,v} V) (e : s.Dart) :
      GeometricStep s (ofMolecule (eraseBond s.graph e))
  | delete (s : State.{u,v} V) (k : AppbPatternKind) (r : AppbRealization s.graph k.pattern) :
      GeometricStep s (ofMolecule r.post)
  | common (s : State.{u,v} V) (r : AppbRealization s.graph appbR23Common) :
      GeometricStep s (ofMolecule r.post)
  | reinsertS33 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.s33.pattern) :
      GeometricStep s (ofMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩))
  | reinsertD33 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.d33.pattern) :
      GeometricStep s (ofMolecule (r.directedPostWithBond 3 4 ⟨2,by decide⟩))
  | r32 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.r3.pattern)
      (t : AppbRealization r.post AppbPatternKind.s33new3.pattern) :
      GeometricStep s (ofMolecule t.post)

private theorem directed_bonds {D : Type u} [Fintype D] [DecidableEq D]
    {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)
    (a b : ℕ) (i : Fin P.edges.length) :
    (r.directedPostWithBond a b i).bonds.card = r.post.bonds.card+1 := by
  unfold AppbRealization.directedPostWithBond
  split_ifs <;> exact r.postWithBond_bonds _ _

theorem GeometricStep.bondPotential_lt {s t : State.{u,v} V} (h : GeometricStep s t) :
    t.bondPotential < s.bondPotential := by
  cases h with
  | bridge e =>
    change (eraseBond s.graph e).bonds.card < s.graph.bonds.card
    have hh := appb_eraseBond_card_bonds s.graph e
    omega
  | delete k r =>
    change r.post.bonds.card < s.graph.bonds.card
    have hh := r.post_card_bonds
    have hp : 0 < k.pattern.edges.length := by cases k <;> decide
    omega
  | common r =>
    change r.post.bonds.card < s.graph.bonds.card
    have hh := r.post_card_bonds
    have hp : appbR23Common.edges.length = 4 := rfl
    omega
  | reinsertS33 r =>
    change (r.directedPostWithBond 3 5 ⟨1,by decide⟩).bonds.card < s.graph.bonds.card
    have hh := r.post_card_bonds
    have hb := directed_bonds r 3 5 ⟨1,by decide⟩
    have he : AppbPatternKind.s33.pattern.edges.length = 5 := rfl
    omega
  | reinsertD33 r =>
    change (r.directedPostWithBond 3 4 ⟨2,by decide⟩).bonds.card < s.graph.bonds.card
    have hh := r.post_card_bonds
    have hb := directed_bonds r 3 4 ⟨2,by decide⟩
    have he : AppbPatternKind.d33.pattern.edges.length = 4 := rfl
    omega
  | r32 r t =>
    change t.post.bonds.card < s.graph.bonds.card
    have hh := (appb_r32_counts s.graph r t).2
    omega

end WaveTurbulence.Mole.AppbAlgorithm

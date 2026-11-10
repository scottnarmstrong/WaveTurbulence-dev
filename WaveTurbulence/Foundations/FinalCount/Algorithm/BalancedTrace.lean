/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.FineGeometryStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedConsecutiveD33
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedTerminalD33
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedReinsertion
import Mathlib.Tactic

/-! # Resource accounting for actual normal chains and controlled deletions

This is a conditional run interface. It does not construct the source
scheduler, classify controlled steps as good, or bound their number.
Every constructor contains actual graph data; no increment inequality is
an input. The source scheduler will have to supply the appropriate run.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive BalancedStep : State.{u,v} V → State.{u,v} V → ℕ → ℕ → Prop
  | normal {s t : State.{u,v} V} (h : NormalGeometryStep s t 1)
      (hM : s.graph.IsMolecule) (hno : AppbNoLoops s.graph) : BalancedStep s t 1 0
  | fine {s t : State.{u,v} V} (h : FineGeometryStep s t)
      (hM : s.graph.IsMolecule) : BalancedStep s t 0 1
  | delete (s : State.{u,v} V) (k : AppbPatternKind)
      (r : AppbRealization s.graph k.pattern) (hM : s.graph.IsMolecule) :
      BalancedStep s (ofMolecule r.post) 0 1
  | interior (s : State.{u,v} V)
      (r : AppbRealization s.graph AppbPatternKind.d33.pattern)
      (t : AppbRealization r.post AppbPatternKind.d33.pattern)
      (hno : AppbNoLoops s.graph) (hb : ∀ e : s.Dart,¬Degen.IsBridge s.graph e)
      (hd : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
        a ∉ AppbPatternKind.d33.pattern.removed → s.graph.deg (r.vertex a) = 4)
      (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4)
      (h3 : r.post.deg (t.vertex 3) = 4) (h4 : r.post.deg (t.vertex 4) = 4) :
      BalancedStep s (ofMolecule r.post) 0 0
  | terminalRung (s : State.{u,v} V)
      (r : AppbRealization s.graph AppbPatternKind.d33.pattern)
      (hno : AppbNoLoops s.graph) (hb : ∀ e : s.Dart,¬Degen.IsBridge s.graph e)
      (hd : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
        a ∉ AppbPatternKind.d33.pattern.removed → s.graph.deg (r.vertex a) = 4)
      (hregular : ∀ b ∈ s.graph.atoms,s.graph.SameComponent (r.vertex 1) b →
        b ∉ r.removedAtoms → s.graph.deg b = 4)
      (hn : ¬∃ q : AppbRealization s.graph AppbPatternKind.d33new.pattern,
        q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
        q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4) :
      BalancedStep s (ofMolecule r.post) 0 0
  | reinsertS33 (s : State.{u,v} V)
      (r : AppbRealization s.graph AppbPatternKind.s33.pattern) (hM : s.graph.IsMolecule)
      (hp : r.post.SameComponent (r.vertex 3) (r.vertex 5)) :
      BalancedStep s (ofMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩)) 0 1
  | reinsertD33 (s : State.{u,v} V)
      (r : AppbRealization s.graph AppbPatternKind.d33.pattern) (hM : s.graph.IsMolecule)
      (hp : r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
      BalancedStep s (ofMolecule (r.directedPostWithBond 3 4 ⟨2,by decide⟩)) 0 1
  | r32 (s : State.{u,v} V)
      (r : AppbRealization s.graph AppbPatternKind.r3.pattern)
      (t : AppbRealization r.post AppbPatternKind.s33new3.pattern) (hM : s.graph.IsMolecule) :
      BalancedStep s (ofMolecule t.post) 0 1

theorem BalancedStep.potential_bound {s t : State.{u,v} V} {n c : ℕ}
    (h : BalancedStep s t n c) :
    balancedPotential s.graph+2*(n : ℤ)-16000*(c : ℤ) ≤ balancedPotential t.graph := by
  cases h with
  | normal h hM hno => have hh := h.nonladder_balanced_gain hM hno; simp only [Nat.cast_one,Nat.cast_zero,mul_one,mul_zero] at *; omega
  | fine h hM => have hh := h.balanced_drop_le hM; simp only [Nat.cast_one,Nat.cast_zero,mul_one,mul_zero]; omega
  | delete k r hM =>
    have hh := pattern_deletion_balanced_drop_le s.graph hM k r
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(1 : ℤ) ≤ balancedPotential r.post
    omega
  | interior r t hno hb hd h1 h2 h3 h4 =>
    have hh := consecutive_d33_balanced_nondecrease s.graph hno r t hb hd h1 h2 h3 h4
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(0 : ℤ) ≤ balancedPotential r.post
    omega
  | terminalRung r hno hb hd hregular hn =>
    have hh := terminal_d33_balanced_nondecrease s.graph hno r hb hd hregular hn
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(0 : ℤ) ≤ balancedPotential r.post
    omega
  | reinsertS33 r hM hp =>
    have hh := directedPostWithBond_balanced_drop_le s.graph hM .s33 r 3 5 ⟨1,by decide⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) hp
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(1 : ℤ) ≤ balancedPotential (r.directedPostWithBond 3 5 ⟨1,by decide⟩)
    omega
  | reinsertD33 r hM hp =>
    have hh := directedPostWithBond_balanced_drop_le s.graph hM .d33 r 3 4 ⟨2,by decide⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) hp
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(1 : ℤ) ≤ balancedPotential (r.directedPostWithBond 3 4 ⟨2,by decide⟩)
    omega
  | r32 r t hM =>
    have hh := r32_balanced_drop_le s.graph hM r t
    change balancedPotential s.graph+2*(0 : ℤ)-16000*(1 : ℤ) ≤ balancedPotential t.post
    omega

end WaveTurbulence.Mole.AppbAlgorithm

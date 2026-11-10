/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ScanMode
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedConsecutiveD33
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedTerminalD33
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33DoubleContinuation
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
import Mathlib.Tactic

/-! # Source graph data for a normal double-rung operation

The stage records the source tests, never a potential inequality or an
operation-count conclusion. The output mode and resource consequences are
proved from those actual tests.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive ZeroNormalStage {D : Type u} [Fintype D] [DecidableEq D]
    {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern)
  | continuing (h : D33Continues r) : ZeroNormalStage r
  | terminalRung (hc : ¬D33Continues r) (hn : ¬HasD33New r) (ht : ¬HasD33ResidualCommon r)
      (hreg : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4) :
      ZeroNormalStage r

structure ZeroNormalData (s : State.{u,v} V) where
  figure : AppbRealization s.graph AppbPatternKind.d33.pattern
  opposite : AppbD33BoundaryOpposite s.graph figure
  noBridges : ∀ e : s.Dart,¬Degen.IsBridge s.graph e
  connected : ∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b
  stage : ZeroNormalStage figure

def ZeroNormalData.target {s : State.{u,v} V} (h : ZeroNormalData s) : State.{u,v} V := ofMolecule h.figure.post

def ZeroNormalData.charge {s : State.{u,v} V} (h : ZeroNormalData s) : ℕ :=
  match h.stage with
  | .continuing _ => 0
  | .terminalRung _ _ _ _ => 1

theorem ZeroNormalData.boundary_four {s : State.{u,v} V} (h : ZeroNormalData s) :
    ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
      a ∉ AppbPatternKind.d33.pattern.removed → s.graph.deg (h.figure.vertex a) = 4 := by
  cases h.stage with
  | continuing hc => exact d33_boundary_four_table h.figure hc.boundary_four.1 hc.boundary_four.2
  | terminalRung hc hn ht hreg => exact d33_terminal_boundary_four h.figure hreg

/-- The graph resource charge is zero precisely for the continuing stage;
the terminal normal rung has the explicit loss two. -/
theorem ZeroNormalData.active_change {s : State.{u,v} V} (h : ZeroNormalData s)
    (hM : s.graph.IsMolecule) (hno : AppbNoLoops s.graph) :
    activeLinkPotential h.target.graph = activeLinkPotential s.graph-2*(h.charge : ℤ) := by
  have hd3 := h.boundary_four 3 (by decide) (by decide)
  have hd4 := h.boundary_four 4 (by decide) (by decide)
  cases hs : h.stage with
  | continuing hc =>
    have hh := d33_normal_activePotential_change_by_rung s.graph hM h.figure hd3 hd4 h.opposite
    rw [if_pos hc.double_boundary] at hh
    change activeLinkPotential h.figure.post = activeLinkPotential s.graph-2*(h.charge : ℤ)
    have hch : h.charge = 0 := by simp only [ZeroNormalData.charge,hs]
    rw [hch]
    simpa only [Nat.cast_zero,mul_zero] using hh
  | terminalRung hc hn ht hreg =>
    have hh := d33_terminal_activePotential_change s.graph hM hno h.figure hd3 hd4 h.opposite hc ht
    change activeLinkPotential h.figure.post = activeLinkPotential s.graph-2*(h.charge : ℤ)
    have hch : h.charge = 1 := by simp only [ZeroNormalData.charge,hs]
    rw [hch]
    simpa only [Nat.cast_one,mul_one] using hh

end WaveTurbulence.Mole.AppbAlgorithm

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ZeroNormalData
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedDeletion
import Mathlib.Tactic

/-! # Resource accounting from the actual normal ladder stage

A regular next boundary gives nondecrease. A defective next boundary
forces the next source residual-defect branch, whose two label outcomes
are good. These are graph facts, not an assumed event-count estimate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def ZeroNormalData.regularNext {s : State.{u,v} V} (h : ZeroNormalData s) : Prop :=
  match h.stage with
  | .continuing hc =>
      let head := LadderHead.afterContinuing h.figure h.connected h.noBridges hc
      h.figure.post.deg (head.figure.vertex 3) = 4 ∧ h.figure.post.deg (head.figure.vertex 4) = 4
  | .terminalRung _ _ _ _ => True

/-- The consecutive-rung proof applies to the actual chosen oriented head;
terminal rungs instead use the proved no-new-figure exclusion. -/
theorem ZeroNormalData.balanced_nondecrease {s : State.{u,v} V} (h : ZeroNormalData s)
    (hno : AppbNoLoops s.graph) (hnext : h.regularNext) :
    balancedPotential s.graph ≤ balancedPotential h.target.graph := by
  change balancedPotential s.graph ≤ balancedPotential h.figure.post
  cases hs : h.stage with
  | continuing hc =>
    let head := LadderHead.afterContinuing h.figure h.connected h.noBridges hc
    have hn : h.figure.post.deg (head.figure.vertex 3) = 4 ∧ h.figure.post.deg (head.figure.vertex 4) = 4 := by
      simpa only [ZeroNormalData.regularNext,hs] using hnext
    have hhds := LadderHead.afterContinuing_heads h.figure h.connected h.noBridges hc
    have hh := consecutive_d33_balanced_nondecrease s.graph hno h.figure head.figure h.noBridges h.boundary_four
      hhds.1 hhds.2 hn.1 hn.2
    omega
  | terminalRung hc hn ht hreg =>
    have hh := terminal_d33_balanced_nondecrease s.graph hno h.figure h.noBridges h.boundary_four hreg hn
    omega

/-- An exceptional preceding normal rung has a bounded actual local loss;
its later charging uses the source defective-boundary implication. -/
theorem ZeroNormalData.balanced_drop_le {s : State.{u,v} V} (h : ZeroNormalData s)
    (hM : s.graph.IsMolecule) :
    balancedPotential s.graph-16000 ≤ balancedPotential h.target.graph := by
  change balancedPotential s.graph-16000 ≤ balancedPotential h.figure.post
  have hh := pattern_deletion_balanced_drop_le s.graph hM .d33 h.figure
  omega

end WaveTurbulence.Mole.AppbAlgorithm

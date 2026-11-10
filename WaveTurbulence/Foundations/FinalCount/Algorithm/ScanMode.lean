/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33SwapHeads
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ContinuationInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33PostConnected
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TerminalRungNextPriority
import Mathlib.Tactic

/-! # Actual source scan modes and their proved transitions

A continuing ladder bypasses a restarted global scan. After a terminal
normal rung, scanning stays in its current component and cannot select
another degree-three double pair. Global forest scans are separate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

structure LadderHead (s : State.{u,v} V) where
  figure : AppbRealization s.graph AppbPatternKind.d33.pattern
  opposite : AppbD33BoundaryOpposite s.graph figure
  noBridges : ∀ e : s.Dart,¬Degen.IsBridge s.graph e
  connected : ∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b

/-- The next displayed head is an actual oriented realization, with
bridgelessness and connectedness derived from the old source graph. -/
noncomputable def LadderHead.afterContinuing {D : Type u} [Fintype D] [DecidableEq D]
    {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (h : D33Continues r) : LadderHead (ofMolecule r.post) := by
  classical
  let t := Classical.choose h.oriented
  have ht := Classical.choose_spec h.oriented
  exact {
    figure := t
    opposite := ht.2.2
    noBridges := h.no_new_bridge hb
    connected := d33_post_connected M r hc hb }

/-- Both orientations of the existential continuation witness are
converted to the source's ordered labels before the next operation. -/
theorem LadderHead.afterContinuing_heads {D : Type u} [Fintype D] [DecidableEq D]
    {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (h : D33Continues r) :
    (LadderHead.afterContinuing r hc hb h).figure.vertex 1 = r.vertex 3 ∧
      (LadderHead.afterContinuing r hc hb h).figure.vertex 2 = r.vertex 4 := by
  have ht := Classical.choose_spec h.oriented
  exact ⟨ht.1,ht.2.1⟩

end WaveTurbulence.Mole.AppbAlgorithm

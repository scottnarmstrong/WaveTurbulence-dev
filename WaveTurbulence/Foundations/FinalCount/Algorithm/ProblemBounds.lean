/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Problem
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentNormalizedProduct
import Mathlib.Tactic

/-! # Literal count values and clean invariants of inherited problems -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}

theorem Problem.value_lowerGap (p : Problem.{u,v} V d L w c g) (g' : ℝ) (h : g' ≤ g)
    (γ δ C1 : ℝ) : (p.lowerGap g' h).value γ δ C1 = p.value γ δ C1 := rfl

theorem Problem.side_noTripleBonds (p : Problem.{u,v} V d L w c g)
    (hnt : AppbNoTripleBonds p.state.graph) (S : Finset V) (hS : AppbClosedSide p.state.graph S) :
    AppbNoTripleBonds (p.side S hS).state.graph :=
  noTripleBonds_closed_side p.state.graph S hS hnt

theorem Problem.deletion_noTripleBonds (p : Problem.{u,v} V d L w c g)
    (hnt : AppbNoTripleBonds p.state.graph) {B : AppbPattern}
    (r : AppbRealization p.state.graph B) (q : Fin B.edges.length → (Fin d → ℤ)) :
    AppbNoTripleBonds (p.deletion r q).state.graph :=
  appb_eraseAtoms_noTripleBonds p.state.graph r.removedAtoms hnt

/-- Actual component projection weakens any cross-component tests only
through the explicit projection predicates stored in the side problems. -/
theorem Problem.value_le_side_product (p : Problem.{u,v} V d L w c g)
    (S : Finset V) (hS : AppbClosedSide p.state.graph S)
    (γ δ C1 : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) :
    p.value γ δ C1 ≤ (p.side S hS).value γ δ C1*
      (p.side (p.state.graph.atoms \ S) hS.complement).value γ δ C1 :=
  component_linkCountA_upper p.state.graph S hS hL hδ hC γ w p.admissible p.scales p.scales_nonneg

end WaveTurbulence.Mole.AppbAlgorithm

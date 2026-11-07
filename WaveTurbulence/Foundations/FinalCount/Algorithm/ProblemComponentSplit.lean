/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ProblemBounds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentForest
import Mathlib.Tactic

/-! # Every disconnected current problem has a concrete proper component split -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}

/-- The component being processed is literally a closed side of the
actual graph. Both children inherit their physical data by projection,
and their product bounds the original possibly correlated count. -/
theorem Problem.exists_component_split (p : Problem.{u,v} V d L w c g)
    (hconn : ¬∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b)
    (γ δ C1 : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) :
    ∃ (S : Finset V) (hS : AppbClosedSide p.state.graph S),
      S.Nonempty ∧ (p.state.graph.atoms \ S).Nonempty ∧
      (∀ a ∈ (p.side S hS).state.graph.atoms,∀ b ∈ (p.side S hS).state.graph.atoms,
        (p.side S hS).state.graph.SameComponent a b) ∧
      ForestMove [p.state] [(p.side S hS).state,(p.side (p.state.graph.atoms \ S) hS.complement).state] ∧
      p.value γ δ C1 ≤ (p.side S hS).value γ δ C1*
        (p.side (p.state.graph.atoms \ S) hS.complement).value γ δ C1 := by
  classical
  push_neg at hconn
  obtain ⟨a,ha,b,hb,hab⟩ := hconn
  let S := Degen.componentSet p.state.graph a
  have hS : AppbClosedSide p.state.graph S := appb_componentSet_closed p.state.graph a
  have haS : a ∈ S := (Degen.mem_componentSet p.state.graph a a).mpr ⟨ha,Relation.EqvGen.refl _⟩
  have hbR : b ∈ p.state.graph.atoms \ S := mem_sdiff.mpr ⟨hb,fun h => hab
    ((Degen.mem_componentSet p.state.graph a b).mp h).2⟩
  refine ⟨S,hS,⟨a,haS⟩,⟨b,hbR⟩,?_,?_,p.value_le_side_product S hS γ δ C1 hL hδ hC⟩
  · exact component_side_connected p.state.graph a
  · exact ForestMove.split [] [] p.state S hS ⟨a,haS⟩ ⟨b,hbR⟩

end WaveTurbulence.Mole.AppbAlgorithm

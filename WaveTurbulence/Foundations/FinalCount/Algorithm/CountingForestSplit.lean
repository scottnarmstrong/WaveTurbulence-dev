/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ProblemBounds
import Mathlib.Tactic

/-! # Actual decorated component splitting preserves the common reserve -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

noncomputable def CountingForest.split (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S) :
    CountingForest.{u,v} V d L γ η w c B := by
  let Ps := pre++p.side S hS::p.side (p.state.graph.atoms \ S) hS.complement::tail
  have he : (p.side S hS).state.bondPotential+
      (p.side (p.state.graph.atoms \ S) hS.complement).state.bondPotential = p.state.bondPotential := by
    have hh := forestBonds_split p.state S hS
    simpa only [Problem.side,forestBonds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hh
  have hbeq : forestBonds (Ps.map Problem.state) = forestBonds (F.problems.map Problem.state) := by
    dsimp only [Ps]
    rw [hlist]
    simp only [List.map_append,List.map_cons,forestBonds,List.sum_append,List.sum_cons]
    omega
  exact {
    gap := F.gap
    problems := Ps
    mode := .globalScan
    reserve_eq := F.reserve_eq.trans (by unfold forestGapReserve; rw [hbeq]) }

/-- A proper split strictly decreases the existing actual forest measure. -/
theorem CountingForest.split_weight_lt (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S)
    (hn : S.Nonempty) (hc : (p.state.graph.atoms \ S).Nonempty) :
    (F.split pre tail p hlist S hS).weight < F.weight := by
  have hh := (ForestMove.split (pre.map Problem.state) (tail.map Problem.state) p.state S hS hn hc).weight_lt
  change forestWeight ((pre++p.side S hS::p.side (p.state.graph.atoms \ S) hS.complement::tail).map Problem.state) <
    forestWeight (F.problems.map Problem.state)
  rw [hlist]
  simpa only [Problem.side,List.map_append,List.map_cons] using hh

/-- Component projection costs no normalization factor; the original
possibly correlated constraints are bounded by the actual projected product. -/
theorem CountingForest.value_le_split (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S)
    (δ C1 : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) :
    F.value δ C1 ≤ (F.split pre tail p hlist S hS).value δ C1 := by
  have hh := p.value_le_side_product S hS γ δ C1 hL hδ hC
  have hp := mul_le_mul_left (mul_le_mul_right hh ((pre.map fun p => p.value γ δ C1).prod))
    ((tail.map fun p => p.value γ δ C1).prod)
  change (F.problems.map fun p => p.value γ δ C1).prod ≤
    ((pre++p.side S hS::p.side (p.state.graph.atoms \ S) hS.complement::tail).map fun p => p.value γ δ C1).prod
  rw [hlist]
  simpa only [List.map_append,List.prod_append,List.map_cons,List.prod_cons,mul_assoc] using hp

end WaveTurbulence.Mole.AppbAlgorithm

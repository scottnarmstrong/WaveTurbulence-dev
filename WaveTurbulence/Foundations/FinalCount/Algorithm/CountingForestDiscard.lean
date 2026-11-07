/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TerminalCount
import Mathlib.Tactic

/-! # Removing a terminal decorated component costs no count or gap reserve -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

noncomputable def CountingForest.discard (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (ht : Terminal p.state) :
    CountingForest.{u,v} V d L γ η w c B := by
  have he : p.state.bondPotential = 0 := by
    change p.state.graph.bonds.card = 0
    rw [ht,Finset.card_empty]
  have hbeq : forestBonds ((pre++tail).map Problem.state) = forestBonds (F.problems.map Problem.state) := by
    rw [hlist]
    simp only [List.map_append,List.map_cons,forestBonds,List.sum_append,List.sum_cons,he,Nat.zero_add]
  exact {
    gap := F.gap
    problems := pre++tail
    mode := .globalScan
    reserve_eq := F.reserve_eq.trans (by unfold forestGapReserve; rw [hbeq]) }

theorem CountingForest.discard_weight_lt (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (ht : Terminal p.state) :
    (F.discard pre tail p hlist ht).weight < F.weight := by
  have hh := (ForestMove.discard (pre.map Problem.state) (tail.map Problem.state) p.state ht).weight_lt
  change forestWeight ((pre++tail).map Problem.state) < forestWeight (F.problems.map Problem.state)
  rw [hlist]
  simpa only [List.map_append,List.map_cons] using hh

theorem CountingForest.value_le_discard (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (ht : Terminal p.state) (δ C1 : ℝ) :
    F.value δ C1 ≤ (F.discard pre tail p hlist ht).value δ C1 := by
  have hh : p.value γ δ C1 ≤ 1 :=
    terminal_linkCountA_le_one p.state.graph ht L γ δ C1 w p.admissible p.scales
  have hp := mul_le_mul_left (mul_le_mul_right hh ((pre.map fun p => p.value γ δ C1).prod))
    ((tail.map fun p => p.value γ δ C1).prod)
  change (F.problems.map fun p => p.value γ δ C1).prod ≤ ((pre++tail).map fun p => p.value γ δ C1).prod
  rw [hlist]
  simpa only [List.map_append,List.prod_append,List.map_cons,List.prod_cons,mul_one,mul_assoc] using hp

end WaveTurbulence.Mole.AppbAlgorithm

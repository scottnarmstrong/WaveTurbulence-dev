/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestInduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestSplit
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestDiscard
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestReplaceValue
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ProblemBounds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ScanMode
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestProgress
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestAct
import Mathlib.Tactic

/-! # The concrete accounting setting and the component-level branches

`ForestOk` records standing graph invariants only. The potential is the
actual balanced potential of the component graphs, and the slack is
nonzero exactly in a ladder mode whose next boundary is defective.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- Standing invariants of a forest at a dispatch point. -/
def ForestOk (m : ℕ) (F : CountingForest.{u,v} V d L γ η w c B) : Prop :=
  (∀ p ∈ F.problems,AppbNoTripleBonds p.state.graph ∧
    (p.state.graph.atoms.card : ℝ) ≤ (1+Real.log L)^m) ∧
  (match F.mode with
    | .ladder _ _ _ => ∀ q ∈ F.problems,
        ∀ a ∈ q.state.graph.atoms,∀ b ∈ q.state.graph.atoms,q.state.graph.SameComponent a b
    | _ => True)

noncomputable def forestPot (F : CountingForest.{u,v} V d L γ η w c B) : ℤ :=
  forestBalancedPotential F.graphs

/-- Slack for a pending defective ladder boundary. -/
noncomputable def forestSlack (F : CountingForest.{u,v} V d L γ η w c B) : ℤ :=
  match F.mode with
  | .ladder p _ head =>
      if p.state.graph.deg (head.figure.vertex 3) = 4 ∧ p.state.graph.deg (head.figure.vertex 4) = 4
      then 0 else 16000
  | _ => 0

theorem forestSlack_le (F : CountingForest.{u,v} V d L γ η w c B) : forestSlack F ≤ 16000 := by
  unfold forestSlack
  split
  · split_ifs <;> norm_num
  · norm_num

theorem forestSlack_global (F : CountingForest.{u,v} V d L γ η w c B)
    (h : F.mode = .globalScan) : forestSlack F = 0 := by
  unfold forestSlack; rw [h]

/-- Total active-link accounting of the component graphs. -/
noncomputable def forestAct (F : CountingForest.{u,v} V d L γ η w c B) : ℤ :=
  (F.graphs.map stateAct).sum

theorem forestAct_edit (pre tail : List (State.{u,v} V)) (s t : State.{u,v} V) :
    ((pre++t::tail).map stateAct).sum = ((pre++s::tail).map stateAct).sum+(stateAct t-stateAct s) := by
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  ring

theorem forestAct_replace {F G : CountingForest.{u,v} V d L γ η w c B}
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (t : State.{u,v} V)
    (hGg : G.graphs = pre.map Problem.state++t::tail.map Problem.state) {K : ℤ}
    (h : stateAct p.state ≤ stateAct t+K) : forestAct F ≤ forestAct G+K := by
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  have := forestAct_edit (pre.map Problem.state) (tail.map Problem.state) p.state t
  unfold forestAct
  rw [hGg,hFg,this]
  linarith only [h]

theorem forestBase (m : ℕ) (F : CountingForest.{u,v} V d L γ η w c B) (h : F.problems = []) :
    forestPot F+forestSlack F ≤ 0 ∧ forestDefect F ≤ 0 ∧ ¬forestHasBonds F ∧ forestAct F ≤ 0 := by
  have h1 : forestPot F = 0 := by
    simp [forestPot,forestBalancedPotential,CountingForest.graphs,h]
  have h2 : forestSlack F = 0 := by
    unfold forestSlack
    split
    · rename_i p hp head hm
      exact absurd (h ▸ hp) (by simp)
    · rfl
  refine ⟨by omega,?_,?_,?_⟩
  · simp [forestDefect,forestDefectPotential,CountingForest.graphs,h]
  · simp [forestHasBonds,ListBonds,CountingForest.graphs,h]
  · simp [forestAct,CountingForest.graphs,h]

/-- The choice-tree exponent: the total bond count of the forest. -/
noncomputable def forestPhi (F : CountingForest.{u,v} V d L γ η w c B) : ℕ := forestBonds F.graphs

/-- The concrete branch type of the forest accounting. -/
abbrev ForestBr (m : ℕ) (F : CountingForest.{u,v} V d L γ η w c B) : Type _ :=
  ForestBranch (ForestOk m) forestPot forestSlack forestDefect forestAct forestHasBonds forestPhi F

/-- The concrete step datum type of the forest accounting. -/
abbrev ForestStep (m : ℕ) (F : CountingForest.{u,v} V d L γ η w c B) (N KF KG : ℝ≥0∞)
    (δ C1 : ℝ) : Type _ :=
  ForestStepData (ForestOk m) forestPot forestSlack forestDefect forestAct forestHasBonds forestPhi F N KF KG δ C1

end WaveTurbulence.Mole.AppbAlgorithm

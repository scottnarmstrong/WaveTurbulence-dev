/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestSplit
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestDiscard
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestReplaceValue
import Mathlib.Tactic

/-! # Well-founded actual decorated-forest moves

This is the iteration backend, not the source scheduler. Constructors
contain actual component splits, terminal discards or nonempty graph
operation traces, and never assume a measure-decrease conclusion.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

inductive CountingForestMove : CountingForest.{u,v} V d L γ η w c B →
    CountingForest.{u,v} V d L γ η w c B → Prop
  | split (F : CountingForest.{u,v} V d L γ η w c B)
      (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
      (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S)
      (hn : S.Nonempty) (hc : (p.state.graph.atoms \ S).Nonempty) :
      CountingForestMove F (F.split pre tail p hlist S hS)
  | discard (F : CountingForest.{u,v} V d L γ η w c B)
      (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
      (hlist : F.problems = pre++p::tail) (ht : Terminal p.state) :
      CountingForestMove F (F.discard pre tail p hlist ht)
  | replace (F : CountingForest.{u,v} V d L γ η w c B)
      (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
      (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
      {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L) (hg : F.gap-L^(-γ) ≤ g0)
      (mode : ForestScanMode (F.replace pre tail p hlist q tr hn hL hg).problems) :
      CountingForestMove F ((F.replace pre tail p hlist q tr hn hL hg).withMode mode)

theorem CountingForestMove.weight_lt {F G : CountingForest.{u,v} V d L γ η w c B}
    (h : CountingForestMove F G) : G.weight < F.weight := by
  cases h with
  | split pre tail p hlist S hS hn hc => exact F.split_weight_lt pre tail p hlist S hS hn hc
  | discard pre tail p hlist ht => exact F.discard_weight_lt pre tail p hlist ht
  | replace pre tail p hlist q tr hn hL hg mode =>
    rw [CountingForest.weight_withMode]
    exact F.replace_weight_lt pre tail p hlist q tr hn hL hg

theorem countingForestMove_wellFounded :
    WellFounded (fun G F : CountingForest.{u,v} V d L γ η w c B => CountingForestMove F G) :=
  Subrelation.wf (fun {_ _} h => h.weight_lt) (InvImage.wf CountingForest.weight Nat.lt_wfRel.wf)

end WaveTurbulence.Mole.AppbAlgorithm

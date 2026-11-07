/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestReplaceValue
import Mathlib.Tactic

/-! # Replacement that continues a ladder at the replaced component -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

theorem CountingForest.replace_gap_le (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) : (F.replace pre tail p hlist q tr hn hL hg).gap ≤ g0 := by
  have hOld : forestGapReserve B L γ η (pre.map Problem.state++p.state::tail.map Problem.state) = F.gap := by
    simpa only [hlist,List.map_append,List.map_cons] using F.reserve_eq.symm
  have hh := forestGapReserve_trace_loss (pre.map Problem.state) (tail.map Problem.state) tr hn B L γ η hL
  rw [hOld] at hh
  exact hh.trans hg

/-- The replacement whose mode continues a ladder at the new component. -/
noncomputable def CountingForest.replaceLadder (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) (head : LadderHead q.state) : CountingForest.{u,v} V d L γ η w c B :=
  let G := F.replace pre tail p hlist q tr hn hL hg
  { G with
    mode := .ladder (q.lowerGap G.gap (F.replace_gap_le pre tail p hlist q tr hn hL hg)) (by
      exact List.mem_append_right _ List.mem_cons_self) head }

theorem CountingForest.replaceLadder_graphs (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) (head : LadderHead q.state) :
    (F.replaceLadder pre tail p hlist q tr hn hL hg head).graphs =
      pre.map Problem.state++q.state::tail.map Problem.state :=
  F.replace_graphs pre tail p hlist q tr hn hL hg

theorem CountingForest.replaceLadder_weight_lt (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) (head : LadderHead q.state) :
    (F.replaceLadder pre tail p hlist q tr hn hL hg head).weight < F.weight :=
  F.replace_weight_lt pre tail p hlist q tr hn hL hg

theorem CountingForest.replaceLadder_value (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) (head : LadderHead q.state) (δ C1 : ℝ) :
    (F.replaceLadder pre tail p hlist q tr hn hL hg head).value δ C1 =
      (pre.map fun p => p.value γ δ C1).prod*q.value γ δ C1*(tail.map fun p => p.value γ δ C1).prod :=
  F.replace_value pre tail p hlist q tr hn hL hg δ C1

end WaveTurbulence.Mole.AppbAlgorithm

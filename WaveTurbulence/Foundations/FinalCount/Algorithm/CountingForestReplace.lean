/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestTraceReserve
import Mathlib.Tactic

/-! # Replacing one current problem by an actual compound-step output

The output can spend one L^(-γ) of the old gap reserve. Its nonempty actual
trace pays that loss, and all untouched problems are lowered to the same
new reserve. The constructor stores no analytic estimate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

noncomputable def CountingForest.replace (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L)
    (hg : F.gap-L^(-γ) ≤ g0) : CountingForest.{u,v} V d L γ η w c B := by
  let gnew := forestGapReserve B L γ η (pre.map Problem.state++q.state::tail.map Problem.state)
  have hOld : forestGapReserve B L γ η (pre.map Problem.state++p.state::tail.map Problem.state) = F.gap := by
    simpa only [hlist,List.map_append,List.map_cons] using F.reserve_eq.symm
  have hNew : gnew ≤ F.gap-L^(-γ) := by
    have hh := forestGapReserve_trace_loss (pre.map Problem.state) (tail.map Problem.state) tr hn B L γ η hL
    rw [hOld] at hh
    exact hh
  have hTail : gnew ≤ F.gap := by
    have hp := Real.rpow_nonneg hL (-γ)
    linarith only [hNew,hp]
  let Ps := (pre.map fun p => p.lowerGap gnew hTail)++
    q.lowerGap gnew (hNew.trans hg)::(tail.map fun p => p.lowerGap gnew hTail)
  have hGraphs : Ps.map Problem.state = pre.map Problem.state++q.state::tail.map Problem.state := by
    simp only [Ps,List.map_append,List.map_cons,List.map_map,Problem.lowerGap,Function.comp_def]
  exact {
    gap := gnew
    problems := Ps
    mode := .globalScan
    reserve_eq := by rw [hGraphs] }

theorem CountingForest.replace_graphs (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L) (hg : F.gap-L^(-γ) ≤ g0) :
    (F.replace pre tail p hlist q tr hn hL hg).graphs =
      pre.map Problem.state++q.state::tail.map Problem.state := by
  simp only [CountingForest.graphs,CountingForest.replace,List.map_append,List.map_cons,List.map_map,
    Problem.lowerGap,Function.comp_def]

/-- A compound step strictly decreases the forest measure; its actual
trace supplies both bond descent and nonincrease of atom count. -/
theorem CountingForest.replace_weight_lt (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L) (hg : F.gap-L^(-γ) ≤ g0) :
    (F.replace pre tail p hlist q tr hn hL hg).weight < F.weight := by
  have hm := tr.mass_lt hn
  have hs : q.state.mass^2+1 < p.state.mass^2+1 := by
    nlinarith only [hm,Nat.zero_le q.state.mass,Nat.zero_le p.state.mass]
  unfold CountingForest.weight
  rw [F.replace_graphs pre tail p hlist q tr hn hL hg]
  unfold CountingForest.graphs
  rw [hlist]
  simp only [List.map_append,List.map_cons,forestWeight,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  omega

end WaveTurbulence.Mole.AppbAlgorithm

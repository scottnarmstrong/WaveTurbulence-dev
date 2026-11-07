/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestReplace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ProblemBounds
import Mathlib.Tactic

/-! # Analytic transport through an actual decorated-forest replacement

The conditional transport lemma is separate from source operation bounds;
its input local inequality is supplied by the proved source reduction.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

theorem CountingForest.replace_value (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L) (hg : F.gap-L^(-γ) ≤ g0)
    (δ C1 : ℝ) :
    (F.replace pre tail p hlist q tr hn hL hg).value δ C1 =
      (pre.map fun p => p.value γ δ C1).prod*q.value γ δ C1*(tail.map fun p => p.value γ δ C1).prod := by
  simp only [CountingForest.value,CountingForest.replace,List.map_append,List.prod_append,List.map_cons,List.prod_cons,
    List.map_map,Function.comp_def,Problem.value_lowerGap,mul_assoc]

/-- Conditional local-to-forest transport. It uses no division and remains
valid for infinite raw counts, zero post-counts and correlated constraints. -/
theorem CountingForest.value_le_replace_of_local (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    {n : ℕ} (tr : Trace p.state q.state n) (hn : 0 < n) (hL : 0 ≤ L) (hg : F.gap-L^(-γ) ≤ g0)
    (δ C1 : ℝ) (I : ℝ≥0∞) (hlocal : p.value γ δ C1 ≤ I*q.value γ δ C1) :
    F.value δ C1 ≤ I*(F.replace pre tail p hlist q tr hn hL hg).value δ C1 := by
  have hp := mul_le_mul_left (mul_le_mul_right hlocal ((pre.map fun p => p.value γ δ C1).prod))
    ((tail.map fun p => p.value γ δ C1).prod)
  rw [F.replace_value pre tail p hlist q tr hn hL hg δ C1]
  unfold CountingForest.value
  rw [hlist]
  simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons]
  convert hp using 1 <;> ring

theorem CountingForest.value_withMode (F : CountingForest.{u,v} V d L γ η w c B)
    (mode : ForestScanMode F.problems) (δ C1 : ℝ) : (F.withMode mode).value δ C1 = F.value δ C1 := rfl

theorem CountingForest.weight_withMode (F : CountingForest.{u,v} V d L γ η w c B)
    (mode : ForestScanMode F.problems) : (F.withMode mode).weight = F.weight := rfl

end WaveTurbulence.Mole.AppbAlgorithm

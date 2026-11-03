/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.HeapOrderVolume
public import WaveTurbulence.Foundations.Analysis.OscillatoryInterval
public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local forest model for the time-integral lemma

Only branching vertices carry time variables. A parent index is smaller
than its child, which certifies acyclicity. Each vertex has at most three
branching children; its remaining children in the full ternary tree are
leaves, carry no integration variable, and have frequency zero. This local
carrier is independent of the future frozen combinatorial tree API.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Analysis

/-- A finite rooted forest of branching vertices, numbered in parent-first
order, with at most three branching children per vertex. -/
structure TimeForest (n : ℕ) where
  parent : Fin n → Option (Fin n)
  parent_lt : ∀ v p, parent v = some p → p.val < v.val
  arity : ∀ p, (Finset.univ.filter fun v => parent v = some p).card ≤ 3

namespace TimeForest

variable {n : ℕ}

/-- The branching children of a vertex. -/
@[expose] def children (T : TimeForest n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => T.parent w = some v

theorem mem_children (T : TimeForest n) (v w : Fin n) :
    w ∈ T.children v ↔ T.parent w = some v := by
  simp only [children, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The heap-ordered time domain with nonnegative edge gaps `σ`.
A root has the external upper time `t` as its parent. Setting `σ v = 0`
recovers the usual strict heap ordering. -/
@[expose] def timeDomain (T : TimeForest n) (t : ℝ) (σ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {s | (∀ v, 0 ≤ s v ∧ s v ≤ t) ∧ ∀ v,
    match T.parent v with
    | none => s v + σ v < t
    | some p => s v + σ v < s p}

/-- The oscillatory time integral of DH21 Lemma 10.2. Frequencies are the
paper's `α`; the phase contains the factor `π`. -/
@[expose] noncomputable def integral (T : TimeForest n) (t : ℝ) (σ α : Fin n → ℝ) : ℂ :=
  ∫ s in T.timeDomain t σ, ∏ v, Complex.exp ((Real.pi * α v * s v : ℝ) * Complex.I)

/-- A finite unfolding of the frequency recursion. Since every child has
a larger index, `n` unfoldings already include every possible descendant. -/
@[expose] def frequencyAt (T : TimeForest n) (α : Fin n → ℝ) (d : Fin n → Bool) :
    ℕ → Fin n → ℝ
  | 0, v => α v
  | k + 1, v => α v + ∑ w ∈ T.children v, if d w then T.frequencyAt α d k w else 0

/-- The recursively accumulated resonance at a branching vertex. -/
@[expose] def frequency (T : TimeForest n) (α : Fin n → ℝ) (d : Fin n → Bool) (v : Fin n) : ℝ :=
  T.frequencyAt α d n v

private theorem frequencyAt_stable (T : TimeForest n) (α : Fin n → ℝ) (d : Fin n → Bool) :
    ∀ k v, n - v.val ≤ k → T.frequencyAt α d (k + 1) v = T.frequencyAt α d k v := by
  intro k
  induction k with
  | zero =>
      intro v hv
      have := v.isLt
      omega
  | succ k ih =>
      intro v hv
      simp only [frequencyAt]
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hd : d w
      · simp only [hd, ↓reduceIte]
        apply ih
        have hpar := T.parent_lt w v ((T.mem_children v w).mp hw)
        omega
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]

/-- Characterization matching the recursive `q` in DH21 Lemma 10.2:
`q_v = α_v + ∑_{w child of v} d_w q_w`. -/
theorem frequency_eq (T : TimeForest n) (α : Fin n → ℝ) (d : Fin n → Bool) (v : Fin n) :
    T.frequency α d v = α v + ∑ w ∈ T.children v, if d w then T.frequency α d w else 0 := by
  exact (T.frequencyAt_stable α d n v (Nat.sub_le _ _)).symm

end TimeForest
end WaveTurbulence.Analysis

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.CoupledSets
public import WaveTurbulence.Foundations.CountLemmas.SumFiber
public import WaveTurbulence.Foundations.CountLemmas.BroadBand
public import WaveTurbulence.Foundations.Counting.FiniteFibers

/-! # Sum-variable projections for the two chain counting problems -/

public section
open Finset Set
namespace WaveTurbulence.CountLemmas

/-- `false` uses `x+y-v`; `true` uses `x+y-v-z`. -/
@[expose] def sumTripleProjection {d : ℕ} (nv : Fin d → ℤ) (sel : Bool)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    (Fin d → ℤ) × (Fin d → ℤ) :=
  (q.1+q.2.1-nv-(if sel then q.2.2 else 0),q.2.2)

/-- Conservation of the projection reconstructs the sum of the first two
variables. -/
theorem sumTripleProjection_sum {d : ℕ} (nv : Fin d → ℤ) (sel : Bool)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) (h : sumTripleProjection nv sel q = p) :
    q.1+q.2.1 = p.1+nv+(if sel then p.2 else 0) := by
  have hx := congrArg Prod.fst h
  have hz := congrArg Prod.snd h
  change q.2.2 = p.2 at hz
  cases sel <;> simp only [sumTripleProjection,Bool.false_eq_true,ite_false,ite_true] at hx ⊢
  · rw [← hx]; abel
  · rw [← hz,← hx]; abel

/-- Pair coordinates are injective on each fixed projection fiber. -/
theorem sumTripleProjection_pair_injOn {d : ℕ} (nv : Fin d → ℤ) (sel : Bool)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Set.InjOn (fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (q.1,q.2.1))
      ((s.filter (fun q => sumTripleProjection nv sel q = p)) : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) := by
  intro q hq r hr he
  have hz := congrArg Prod.snd ((mem_filter.mp hq).2.trans (mem_filter.mp hr).2.symm)
  have hx : q.1 = r.1 := congrArg (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1) he
  have hy : q.2.1 = r.2.1 := congrArg (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.2) he
  change q.2.2 = r.2.2 at hz
  exact Prod.ext hx (Prod.ext hy hz)

/-- Norm control for the free projected variable uses only the three
source unit balls. The radius-four counting API leaves harmless slack. -/
theorem sumTripleProjection_norm {d : ℕ} (L : ℝ) (a b c : Mom d)
    (nv : Fin d → ℤ) (sel : Bool)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (ha : NearLattice L a q.1) (hb : NearLattice L b q.2.1) (hc : NearLattice L c q.2.2) :
    ‖latticePoint L (sumTripleProjection nv sel q).1-
      (a+b-latticePoint L nv-(if sel then c else 0))‖ ≤ 4 := by
  change ‖latticePoint L q.1-a‖ ≤ 1 at ha
  change ‖latticePoint L q.2.1-b‖ ≤ 1 at hb
  change ‖latticePoint L q.2.2-c‖ ≤ 1 at hc
  dsimp only [sumTripleProjection]
  rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_add_eq]
  cases sel
  · simp only [Bool.false_eq_true,ite_false,sub_zero]
    have hz : latticePoint L (0 : Fin d → ℤ) = 0 := by ext i; simp [latticePoint]
    rw [hz,sub_zero]
    have heq : (latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv)-
        (a+b-latticePoint L nv) = (latticePoint L q.1-a)+(latticePoint L q.2.1-b) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith only [ha,hb])
  · simp only [ite_true]
    have heq : (latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv-latticePoint L q.2.2)-
        (a+b-latticePoint L nv-c) =
        ((latticePoint L q.1-a)+(latticePoint L q.2.1-b))-(latticePoint L q.2.2-c) := by abel
    rw [heq]
    calc
      _ ≤ ‖(latticePoint L q.1-a)+(latticePoint L q.2.1-b)‖+‖latticePoint L q.2.2-c‖ := norm_sub_le _ _
      _ ≤ (‖latticePoint L q.1-a‖+‖latticePoint L q.2.1-b‖)+‖latticePoint L q.2.2-c‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 4 := by linarith only [ha,hb,hc]

end WaveTurbulence.CountLemmas

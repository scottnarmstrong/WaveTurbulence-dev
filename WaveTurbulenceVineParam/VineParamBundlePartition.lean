/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamOrientationCounts
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Multiset.Replicate
import Mathlib.Tactic

/-! # Exact directed bond partition by distinct unordered bundles

The normal form groups actual directed occurrences without discarding their
orientations or multiplicities. It is the combinatorial normalization step
before applying the finite base orientation classification.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-- One unordered bundle retains the actual counts in its two directions. -/
@[expose] def directedBundle (A : Multiset (α×α)) (p : α×α) : Multiset (α×α) :=
  Multiset.replicate (A.count p) p+
    Multiset.replicate (A.count (p.2,p.1)) (p.2,p.1)

/-- Counting commutes with finite multiset addition. -/
theorem count_finset_sum {β : Type*} [DecidableEq β] {κ : Type*}
    (s : Finset κ) (f : κ → Multiset β) (b : β) :
    (∑ i ∈ s,f i).count b=∑ i ∈ s,(f i).count b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,Multiset.count_zero]
  | @insert a s ha ih => simp only [sum_insert ha,Multiset.count_add,ih]

/-- A directed bundle contributes exactly the actual count of a queried
ordered pair if its unordered endpoints agree, and zero otherwise. -/
theorem count_directedBundle (A : Multiset (α×α)) (p q : α×α) (hp : p.1 ≠ p.2) :
    (directedBundle A p).count q=if s(p.1,p.2)=s(q.1,q.2) then A.count q else 0 := by
  have he : s(p.1,p.2)=s(q.1,q.2) ↔ p=q ∨ (p.2,p.1)=q := by
    constructor
    · intro h
      have hh := Sym2.eq_iff.mp h
      change (p.1=q.1 ∧ p.2=q.2) ∨ (p.1=q.2 ∧ p.2=q.1) at hh
      exact hh.elim (fun h => Or.inl (Prod.ext h.1 h.2))
        (fun h => Or.inr (Prod.ext h.2 h.1))
    · rintro (rfl | h)
      · rfl
      · rw [← h]; exact Sym2.eq_swap
  have hne : p ≠ (p.2,p.1) := fun h => hp (congrArg Prod.fst h)
  simp only [directedBundle,Multiset.count_add,Multiset.count_replicate,he]
  by_cases h1 : p=q <;> by_cases h2 : (p.2,p.1)=q <;> simp_all

/-- Every actual directed occurrence belongs to exactly one unordered
bundle, so grouping it by the actual direction counts is an exact equality. -/
theorem directed_bundle_partition (A : Multiset (α×α)) (b : ι → α×α)
    (hb : ∀ i,(b i).1 ≠ (b i).2)
    (hinj : Function.Injective (fun i => s((b i).1,(b i).2)))
    (hcover : ∀ q ∈ A,∃ i,s((b i).1,(b i).2)=s(q.1,q.2)) :
    A=∑ i,directedBundle A (b i) := by
  apply Multiset.ext.mpr
  intro q
  rw [count_finset_sum]
  simp_rw [count_directedBundle A _ q (hb _)]
  by_cases hq : q ∈ A
  · obtain ⟨i,hi⟩ := hcover q hq
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi]
    · intro j _hj hji
      have hn : s((b j).1,(b j).2) ≠ s(q.1,q.2) := by
        intro hj
        exact hji (hinj (hj.trans hi.symm))
      exact ite_eq_right hn
    · intro hn
      exact False.elim (hn (mem_univ i))
  · have hz : A.count q=0 := Multiset.count_eq_zero.mpr hq
    simp only [hz,ite_self,sum_const_zero]

end WaveTurbulence.Vine.Param

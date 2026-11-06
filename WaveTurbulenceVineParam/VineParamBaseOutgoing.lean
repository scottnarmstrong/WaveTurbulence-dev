/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBaseDirectionCounts
public import WaveTurbulenceVineParam.VineParamProfileClassification
import Mathlib.Tactic

/-! # Actual outgoing degrees select a complete base orientation profile -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- The actual outgoing count at an atom in a directed endpoint multiset. -/
@[expose] def outgoingCount (A : Multiset (ℕ×ℕ)) (v : ℕ) : ℕ :=
  A.countP (fun p => p.1=v)

/-- Predicate counting commutes with finite multiset addition. -/
theorem countP_finset_sum {α ι : Type*} (p : α → Prop) [DecidablePred p]
    (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s,f i).countP p=∑ i ∈ s,(f i).countP p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,Multiset.countP_zero]
  | @insert a s ha ih => simp only [sum_insert ha,Multiset.countP_add,ih]

/-- Predicate counting on a repeated occurrence is its actual multiplicity. -/
theorem countP_replicate {α : Type*} (p : α → Prop) [DecidablePred p] (a : α) (n : ℕ) :
    (Multiset.replicate n a).countP p=if p a then n else 0 := by
  by_cases hp : p a
  · induction n with
    | zero => simp only [Multiset.replicate_zero,Multiset.countP_zero,ite_true,hp]
    | succ n ih =>
      rw [Multiset.replicate_succ,Multiset.countP_cons_of_pos _ hp,ih]
      simp only [hp,ite_true]
  · induction n with
    | zero => simp only [Multiset.replicate_zero,Multiset.countP_zero,ite_false,hp]
    | succ n ih =>
      rw [Multiset.replicate_succ,Multiset.countP_cons_of_neg _ hp,ih]
      simp only [hp,ite_false]

/-- One non-loop bundle contributes the actual forward count at its first
endpoint and the actual reverse count at its second. -/
theorem outgoingCount_directedBundle (A : Multiset (ℕ×ℕ)) (p : ℕ×ℕ) (v : ℕ)
    (hp : p.1 ≠ p.2) :
    outgoingCount (directedBundle A p) v=
      if p.1=v then A.count p else if p.2=v then A.count (p.2,p.1) else 0 := by
  simp only [outgoingCount,directedBundle,Multiset.countP_add,countP_replicate]
  by_cases h1 : p.1=v <;> by_cases h2 : p.2=v <;> simp_all

/-- The generic source-degree polynomial is exactly the outgoing count of
actual directed bonds; its variables are the actual forward counts. -/
theorem baseOutgoing_eq_actual (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))) (v : ℕ) :
    baseOutgoing X (fun i => A.count (baseBundlePair X i)) v=outgoingCount A v := by
  conv_rhs => rw [base_directed_partition X A hU]
  rw [outgoingCount,countP_finset_sum]
  apply sum_congr rfl
  intro i _hi
  have hp := baseBundles_endpoints X ((baseBundles X)[i.1]'i.2) (List.getElem_mem i.2)
  have he := outgoingCount_directedBundle A (baseBundlePair X i) v (Nat.ne_of_lt hp.1)
  rw [base_reverse_count X A hU i] at he
  exact he.symm

/-- Actual source degrees and undirected template matching produce a profile
in the exhaustive catalogue, without a preselected directed template. -/
theorem exists_actual_base_profile (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hdeg : ∀ v : Fin X.template.n,outgoingCount A v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount X),baseProfileCounts X p=
      List.ofFn (fun i => A.count (baseBundlePair X i)) := by
  apply exists_base_profile X _ (base_forward_count_le X A hU)
  intro v
  rw [baseOutgoing_eq_actual X A hU v.1]
  exact hdeg v

end WaveTurbulence.Vine.Param

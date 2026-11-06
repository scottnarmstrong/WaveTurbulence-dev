/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBaseBundlePartition
import Mathlib.Tactic

/-! # Source multiplicity bounds and reverse counts for actual base orientations -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Unordered counts split into the two actual directions for distinct atoms. -/
theorem unordered_multiset_count (A : Multiset (ℕ×ℕ)) (u v : ℕ) (hne : u ≠ v) :
    (A.map (fun p => s(p.1,p.2))).count s(u,v)=A.count (u,v)+A.count (v,u) := by
  induction A using Quotient.inductionOn with
  | h l =>
    change ((l : Multiset (ℕ×ℕ)).map (fun p => s(p.1,p.2))).count s(u,v)=
      (l : Multiset (ℕ×ℕ)).count (u,v)+(l : Multiset (ℕ×ℕ)).count (v,u)
    simpa only [Multiset.map_coe,Multiset.coe_count] using unordered_pair_count l u v hne

/-- Actual forward and reverse counts sum to the pinned bundle multiplicity. -/
theorem base_direction_count_sum (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (i : Fin (baseBundles X).length) :
    A.count (baseBundlePair X i)+A.count ((baseBundlePair X i).2,(baseBundlePair X i).1)=
      ((baseBundles X)[i.1]'i.2).2 := by
  have hb := baseBundles_endpoints X ((baseBundles X)[i.1]'i.2) (List.getElem_mem i.2)
  have hne : (baseBundlePair X i).1 ≠ (baseBundlePair X i).2 := Nat.ne_of_lt hb.1
  have hh := congrArg (Multiset.count s((baseBundlePair X i).1,(baseBundlePair X i).2)) hU
  rw [unordered_multiset_count A _ _ hne] at hh
  rw [Multiset.coe_count,baseBundle_template_count X i] at hh
  exact hh

/-- The actual forward counts satisfy the only multiplicity bounds assumed
by the exhaustive source degree classification. -/
theorem base_forward_count_le (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))) :
    ∀ i : Fin (baseBundles X).length,A.count (baseBundlePair X i) ≤ ((baseBundles X)[i.1]'i.2).2 := by
  intro i
  have := base_direction_count_sum X A hU i
  omega

/-- Every reverse count is exactly the complement of the actual forward count. -/
theorem base_reverse_count (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (i : Fin (baseBundles X).length) :
    A.count ((baseBundlePair X i).2,(baseBundlePair X i).1)=
      ((baseBundles X)[i.1]'i.2).2-A.count (baseBundlePair X i) := by
  have := base_direction_count_sum X A hU i
  omega

/-- Unordered source shape and actual forward counts determine the entire
oriented multiset, including every parallel occurrence. -/
theorem base_ordered_eq_of_counts (X : VineType) (A B : Multiset (ℕ×ℕ))
    (hA : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hB : B.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hc : ∀ i : Fin (baseBundles X).length,A.count (baseBundlePair X i)=B.count (baseBundlePair X i)) :
    A=B := by
  rw [base_directed_partition X A hA,base_directed_partition X B hB]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [directedBundle,base_reverse_count X A hA i,base_reverse_count X B hB i,hc i]

end WaveTurbulence.Vine.Param

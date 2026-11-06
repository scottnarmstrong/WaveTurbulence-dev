/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBundlePartition
public import WaveTurbulenceVineParam.VineParamProfileDegrees
import Mathlib.Tactic

/-! # Actual directed occurrences partition into the pinned base bundles -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- The canonical endpoint pair for one unordered base bundle. -/
@[expose] def baseBundlePair (X : VineType) (i : Fin (baseBundles X).length) : ℕ×ℕ :=
  ((baseBundles X)[i.1]'i.2).1

/-- The list has one entry for each distinct unordered parallel bundle. -/
theorem baseBundleKey_injective (X : VineType) :
    Function.Injective (fun i : Fin (baseBundles X).length =>
      s((baseBundlePair X i).1,(baseBundlePair X i).2)) := by
  cases X <;> decide

/-- Every literal source bond belongs to one of these bundles. -/
theorem baseBundle_covers_template (X : VineType) :
    ∀ i : Fin X.template.bonds.length,∃ j : Fin (baseBundles X).length,
      s((baseBundlePair X j).1,(baseBundlePair X j).2)=
        s((X.template.bonds[i.1]'i.2).1,(X.template.bonds[i.1]'i.2).2) := by
  cases X <;> decide

/-- A source bundle has exactly its recorded multiplicity in the template. -/
theorem baseBundle_template_count (X : VineType) :
    ∀ i : Fin (baseBundles X).length,
      (X.template.bonds.map (fun e => s(e.1,e.2))).count
        s((baseBundlePair X i).1,(baseBundlePair X i).2)=((baseBundles X)[i.1]'i.2).2 := by
  cases X <;> decide

/-- Unordered matching alone forces every actual directed occurrence into
one pinned bundle, without choosing any direction in advance. -/
theorem baseBundle_covers_actual (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))) :
    ∀ q ∈ A,∃ j : Fin (baseBundles X).length,
      s((baseBundlePair X j).1,(baseBundlePair X j).2)=s(q.1,q.2) := by
  intro q hq
  have hm : s(q.1,q.2) ∈ A.map (fun e => s(e.1,e.2)) := Multiset.mem_map.mpr ⟨q,hq,rfl⟩
  rw [hU] at hm
  change s(q.1,q.2) ∈ (X.template.bonds : Multiset (ℕ×ℕ)).map (fun e => s(e.1,e.2)) at hm
  obtain ⟨p,hp,he⟩ := Multiset.mem_map.mp hm
  have hp' : p ∈ X.template.bonds := hp
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp'
  obtain ⟨j,hj⟩ := baseBundle_covers_template X i
  refine ⟨j,?_⟩
  have hi' : (X.template.bonds[i.1]'i.2)=p := hi
  rw [hi'] at hj
  exact hj.trans he

/-- The full actual directed bond multiset is recovered from its two counts
in every pinned unordered bundle. -/
theorem base_directed_partition (X : VineType) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))) :
    A=∑ i : Fin (baseBundles X).length,directedBundle A (baseBundlePair X i) := by
  apply directed_bundle_partition A (baseBundlePair X)
  · intro i
    exact Nat.ne_of_lt (baseBundles_endpoints X _ (List.getElem_mem _)).1
  · exact baseBundleKey_injective X
  · exact baseBundle_covers_actual X A hU

end WaveTurbulence.Vine.Param

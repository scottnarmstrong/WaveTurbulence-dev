/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupPartition
import Mathlib.Tactic

/-! # Coherence groups persist and every new group has a slot allocation -/

public section
namespace WaveTurbulence.Vine

/-- Insertion retains each existing coherence group. -/
theorem insertRungs_group_mem (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k : ℕ) {g : List ℕ} (hg : g ∈ T.groups) : g ∈ (insertRungs T s k).groups := by
  by_cases hk : k=0
  · simpa only [hk,insertRungs_zero] using hg
  · simp only [insertRungs,hk,ite_false]
    exact List.mem_append_left _ hg

/-- Subsequent slots never alter an existing coherence group. -/
theorem fold_group_mem (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    {g : List ℕ} (hg : g ∈ T.groups) :
    g ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups := by
  induction xs generalizing T with
  | nil => exact hg
  | cons sk xs ih => exact ih _ (insertRungs_group_mem T sk.1 sk.2 hg)

/-- Each allocated rung pair appears as a group in the full expansion. -/
theorem fold_allocated_group (T : VineTemplate)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k i : ℕ) (hi : i<k) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n
    [N+i,N+k+i] ∈ ((pre++(s,k)::post).foldl
      (fun U sk => insertRungs U sk.1 sk.2) T).groups := by
  dsimp only
  rw [List.foldl_append,List.foldl_cons]
  apply fold_group_mem
  let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T
  change [U.n+i,U.n+k+i] ∈ (insertRungs U s k).groups
  have hk : k ≠ 0 := by omega
  simp only [insertRungs,hk,ite_false]
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(_, _),?_,rfl⟩
  have hm := List.getElem_mem (l := ((List.range k).map (U.n+·)).zip
      ((List.range k).map (U.n+k+·))) (n := i) (by simpa using hi)
  simpa using hm

/-- Every original group appears unchanged in any expansion. -/
theorem template_group_mem_expand (X : VineType) (ks : List ℕ)
    {g : List ℕ} (hg : g ∈ X.template.groups) : g ∈ (X.expand ks).groups :=
  fold_group_mem _ _ hg

/-- Insertion groups are either retained groups or individual allocated rungs. -/
theorem insertRungs_group_origin (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k : ℕ) {g : List ℕ} (hg : g ∈ (insertRungs T s k).groups) :
    g ∈ T.groups ∨ ∃ i<k,g=[T.n+i,T.n+k+i] := by
  by_cases hk : k=0
  · exact Or.inl (by simpa only [hk,insertRungs_zero] using hg)
  · simp only [insertRungs,hk,ite_false,List.mem_append] at hg
    rcases hg with hg | hg
    · exact Or.inl hg
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
      have hik : i<k := by simpa using hi
      have he' : (T.n+i,T.n+k+i)=p := by simpa using he
      exact Or.inr ⟨i,hik,by rw [← he']⟩

/-- Every expanded group has a unique structural origin: the old core or
one rung of a particular insertion interval. Uniqueness is not needed here. -/
theorem fold_group_origin (T : VineTemplate) (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    {g : List ℕ} (hg : g ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups) :
    g ∈ T.groups ∨ ∃ pre post s k i,xs=pre++(s,k)::post ∧ i<k ∧
      g=[(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n+i,
        (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n+k+i] := by
  induction xs generalizing T with
  | nil => exact Or.inl hg
  | cons sk xs ih =>
    rcases ih (insertRungs T sk.1 sk.2) hg with hg | ⟨pre,post,s,k,i,hloc,hi,hg⟩
    · rcases insertRungs_group_origin T sk.1 sk.2 hg with hg | ⟨i,hi,hg⟩
      · exact Or.inl hg
      · exact Or.inr ⟨[],xs,sk.1,sk.2,i,rfl,hi,hg⟩
    · refine Or.inr ⟨sk::pre,post,s,k,i,?_,hi,hg⟩
      simpa only [List.cons_append] using congrArg (List.cons sk) hloc

end WaveTurbulence.Vine

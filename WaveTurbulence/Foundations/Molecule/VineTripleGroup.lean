/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupPartition
import Mathlib.Tactic

/-! # The unique three-atom group of normal vines (TARGET cohmol) -/

public section
namespace WaveTurbulence.Vine

/-- Number of three-atom groups in a template. -/
@[expose] def numTripleGroups (T : VineTemplate) : ℕ :=
  (T.groups.filter fun g => g.length=3).length

/-- The pinned normal templates have one three-atom group, and the bad
ones have none, exactly as in TARGET cohmol. -/
theorem template_triple_groups (X : VineType) :
    numTripleGroups X.template=if X.IsBad then 0 else 1 := by
  cases X <;> rfl

/-- New rung groups have two atoms and cannot create a triple group. -/
theorem insertRungs_triple_groups (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) :
    numTripleGroups (insertRungs T s k)=numTripleGroups T := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
  · let us := (List.range k).map (T.n+·)
    let vs := (List.range k).map (T.n+k+·)
    have hfilter : (((us.zip vs).map fun p => [p.1,p.2]).filter fun g => g.length=3)=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro g hg
      obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hg
      norm_num
    dsimp only [us,vs] at hfilter
    simp only [numTripleGroups,insertRungs,hk,ite_false,List.filter_append,
      List.length_append,hfilter,List.length_nil,Nat.add_zero]

/-- Triple-group count is invariant through an arbitrary instruction list. -/
theorem fold_triple_groups (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) :
    numTripleGroups (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T)=numTripleGroups T := by
  induction xs generalizing T with
  | nil => rfl
  | cons sk xs ih => rw [List.foldl_cons,ih,insertRungs_triple_groups]

/-- TARGET cohmol: every expanded normal vine has exactly one triple group;
every expanded bad vine has none. -/
theorem expand_triple_groups (X : VineType) (k : List ℕ) :
    numTripleGroups (X.expand k)=if X.IsBad then 0 else 1 := by
  rw [VineType.expand,fold_triple_groups,template_triple_groups]

end WaveTurbulence.Vine

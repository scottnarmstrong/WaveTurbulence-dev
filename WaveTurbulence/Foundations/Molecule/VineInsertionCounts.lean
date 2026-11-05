/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Exact counts under the pinned rung insertion (TARGET defvine)

A slot uses two occurrences of bonds. Its local membership premise below
expresses that those occurrences are present before replacing them.
-/

public section
namespace WaveTurbulence.Vine

/-- The k=0 convention retains the template exactly (F37). -/
theorem insertRungs_zero (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) :
    insertRungs T s 0 = T := by simp only [insertRungs,ite_true]

/-- Each inserted rung adds exactly two atoms. -/
theorem insertRungs_atoms (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) :
    (insertRungs T s k).n = T.n+2*k := by
  by_cases hk : k=0 <;> simp [insertRungs,hk]

/-- Each rail with k interior atoms contains k+1 bonds. -/
theorem railBonds_length (a b : ℕ) (ws : List ℕ) :
    (railBonds a ws b).length = ws.length+1 := by
  simp only [railBonds,List.length_zip,List.length_cons,List.length_append,
    List.length_nil,min_self]

private theorem double_list_length {A : Type*} (xs : List A) :
    (xs.flatMap fun x => [x,x]).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]; omega

/-- Each inserted rung adds four bonds after replacing the two slot bonds. -/
theorem insertRungs_bonds (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1) :
    (insertRungs T s k).bonds.length = T.bonds.length+4*k := by
  by_cases hk : k=0
  · simp [insertRungs,hk]
  · have he1 := List.length_erase_add_one h1
    have he2 := List.length_erase_add_one h2
    simp only [insertRungs,hk,ite_false,List.length_append,railBonds_length,
      double_list_length,List.length_zip,List.length_map,List.length_range,min_self]
    omega

/-- Each rung adds one two-atom coherence group. -/
theorem insertRungs_groups (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) :
    (insertRungs T s k).groups.length = T.groups.length+k := by
  by_cases hk : k=0 <;> simp [insertRungs,hk]

/-- Slot labels are retained so the next distinct slot can be expanded. -/
theorem insertRungs_slots (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) :
    (insertRungs T s k).slots = T.slots := by
  by_cases hk : k=0 <;> simp [insertRungs,hk]

/-- Folded insertion adds two atoms for every inserted rung. -/
theorem fold_insertRungs_atoms (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n =
      T.n+2*(xs.map Prod.snd).sum := by
  induction xs generalizing T with
  | nil => simp
  | cons sk xs ih =>
    simp only [List.foldl_cons,ih,insertRungs_atoms,List.map_cons,List.sum_cons]
    omega

/-- Folded insertion adds one group for every inserted rung. -/
theorem fold_insertRungs_groups (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups.length =
      T.groups.length+(xs.map Prod.snd).sum := by
  induction xs generalizing T with
  | nil => simp
  | cons sk xs ih =>
    simp only [List.foldl_cons,ih,insertRungs_groups,List.map_cons,List.sum_cons]
    omega

/-- The expansion has the template atoms plus twice the total inserted rungs.
The zip convention ignores surplus entries; IsVine requires the exact length. -/
theorem expand_atoms (X : VineType) (k : List ℕ) :
    (X.expand k).n = X.template.n+2*((X.template.slots.zip k).map Prod.snd).sum :=
  fold_insertRungs_atoms _ _

end WaveTurbulence.Vine

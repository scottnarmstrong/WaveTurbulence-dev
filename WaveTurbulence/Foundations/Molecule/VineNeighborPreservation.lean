/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionNeighbors
import Mathlib.Tactic

/-! # Locality of literal rung insertion -/

public section
namespace WaveTurbulence.Vine

/-- Removing an edge with neither endpoint v leaves the neighbor row at v. -/
theorem edgeListNeighbors_erase (es : List (ℕ×ℕ)) (e : ℕ×ℕ) (v : ℕ)
    (h1 : e.1 ≠ v) (h2 : e.2 ≠ v) :
    edgeListNeighbors (es.erase e) v=edgeListNeighbors es v := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    by_cases hp : p=e
    · subst p
      simp only [List.erase_cons_head,edgeListNeighbors_cons,h1,h2,ite_false,zero_add]
    · rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using hp),edgeListNeighbors_cons,ih,edgeListNeighbors_cons]

/-- A later insertion preserves the complete neighbor row of every old atom
away from its four rail endpoints. -/
theorem insertRungs_neighbors_old (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k v : ℕ) (hv : v<T.n)
    (hs : s.1.1 ≠ v ∧ s.1.2 ≠ v ∧ s.2.1 ≠ v ∧ s.2.2 ≠ v) :
    edgeListNeighbors (insertRungs T s k).bonds v=edgeListNeighbors T.bonds v := by
  by_cases hk : k=0
  · simp only [insertRungs,hk,ite_true]
  · have hu : edgeListNeighbors (railBonds s.1.1 ((List.range k).map (T.n+·)) s.1.2) v=0 := by
      apply rail_neighbors_zero _ _ _ _ hs.1 hs.2.1
      intro w hw
      obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hw
      omega
    have hw : edgeListNeighbors (railBonds s.2.1 ((List.range k).map (T.n+k+·)) s.2.2) v=0 := by
      apply rail_neighbors_zero _ _ _ _ hs.2.2.1 hs.2.2.2
      intro w hw
      obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hw
      omega
    have hr : edgeListNeighbors (allocatedRungs T.n (T.n+k) k) v=0 := by
      apply edgeListNeighbors_zero
      intro e he
      obtain ⟨j,_hj,rfl⟩ := allocatedRungs_mem he
      constructor <;> omega
    simp only [insertRungs,hk,ite_false,edgeListNeighbors_append,hu,hw,
      ← allocatedRungs_eq_zip,hr,add_zero]
    rw [edgeListNeighbors_erase _ s.2 v hs.2.2.1 hs.2.2.2,
      edgeListNeighbors_erase _ s.1 v hs.1 hs.2.1]

/-- A list of insertions away from an old vertex preserves its neighbor row.
This applies to an allocated rung once all remaining slot endpoints are old
core atoms. -/
theorem fold_insertRungs_neighbors (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (T : VineTemplate) (v : ℕ) (hv : v<T.n)
    (hx : ∀ sk ∈ xs, sk.1.1.1 ≠ v ∧ sk.1.1.2 ≠ v ∧
      sk.1.2.1 ≠ v ∧ sk.1.2.2 ≠ v) :
    edgeListNeighbors (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds v=
      edgeListNeighbors T.bonds v := by
  induction xs generalizing T with
  | nil => rfl
  | cons sk xs ih =>
    rw [List.foldl_cons,ih]
    · exact insertRungs_neighbors_old T sk.1 sk.2 v hv (hx sk List.mem_cons_self)
    · rw [insertRungs_atoms]
      omega
    · intro z hz
      exact hx z (List.mem_cons_of_mem _ hz)

end WaveTurbulence.Vine

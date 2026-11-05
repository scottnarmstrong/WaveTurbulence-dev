/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSequencePreservation
import Mathlib.Tactic

/-! # Endpoint bounds through literal insertion folds -/

public section
namespace WaveTurbulence.Vine

/-- Every vertex of a bounded rail gives bounded bond endpoints. -/
theorem railBonds_endpoints (a b N : ℕ) (ws : List ℕ) (ha : a<N) (hb : b<N)
    (hw : ∀ w ∈ ws,w<N) {e : ℕ×ℕ} (he : e ∈ railBonds a ws b) :
    e.1<N ∧ e.2<N := by
  obtain ⟨h1,h2⟩ := List.of_mem_zip he
  constructor
  · rcases List.mem_cons.mp h1 with h | h
    · simpa only [h] using ha
    · exact hw _ h
  · rcases List.mem_append.mp h2 with h | h
    · exact hw _ h
    · simpa only [List.mem_singleton.mp h] using hb

/-- No insertion creates an edge with an out-of-range endpoint. -/
theorem insertRungs_endpoints (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n) :
    ∀ p ∈ (insertRungs T s k).bonds,p.1<(insertRungs T s k).n ∧
      p.2<(insertRungs T s k).n := by
  by_cases hk : k=0
  · simpa only [insertRungs,hk,ite_true] using hT
  intro p hp
  rw [insertRungs_atoms]
  simp only [insertRungs,hk,ite_false,List.mem_append,← allocatedRungs_eq_zip] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · have hh := erase_bonds_bounded _ s.2 T.n (erase_bonds_bounded _ s.1 T.n hT) p hp
    constructor <;> omega
  · apply railBonds_endpoints _ _ _ _ (by omega) (by omega) _ hp
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega
  · apply railBonds_endpoints _ _ _ _ (by omega) (by omega) _ hp
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega
  · obtain ⟨i,hi,rfl⟩ := allocatedRungs_mem hp
    constructor <;> omega

/-- A fold of slots whose endpoints belong to the original atom range
keeps every bond endpoint in the allocated range. -/
theorem fold_insertRungs_endpoints (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : ∀ sk ∈ xs,sk.1.1.1<T.n ∧ sk.1.1.2<T.n ∧
      sk.1.2.1<T.n ∧ sk.1.2.2<T.n) :
    ∀ p ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds,
      p.1<(xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n ∧
      p.2<(xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n := by
  induction xs generalizing T with
  | nil => exact hT
  | cons sk xs ih =>
    rw [List.foldl_cons]
    apply ih _ (insertRungs_endpoints T sk.1 sk.2 hT (hs sk List.mem_cons_self))
    intro z hz
    have hh := hs z (List.mem_cons_of_mem _ hz)
    rw [insertRungs_atoms]
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

end WaveTurbulence.Vine

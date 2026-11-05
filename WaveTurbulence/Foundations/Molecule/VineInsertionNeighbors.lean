/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFreshRailNeighbors
public import WaveTurbulence.Foundations.Molecule.VineRungNeighbors
import Mathlib.Tactic

/-! # Fresh neighbor rows in the pinned rung insertion -/

public section
namespace WaveTurbulence.Vine

/-- Erasing edges preserves a bound on their endpoint names. -/
theorem erase_bonds_bounded (es : List (ℕ×ℕ)) (e : ℕ×ℕ) (n : ℕ)
    (h : ∀ p ∈ es,p.1<n ∧ p.2<n) :
    ∀ p ∈ es.erase e,p.1<n ∧ p.2<n := by
  intro p hp
  exact h p (List.mem_of_mem_erase hp)

/-- Fresh left-rail vertex: two rail neighbors and its doubled rung partner.
The hypotheses are only the old endpoint bounds of the pinned template. -/
theorem insertRungs_neighbors_left (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k i : ℕ) (hi : i<k)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n) :
    edgeListNeighbors (insertRungs T s k).bonds (T.n+i)=
      ({if i=0 then s.1.1 else T.n+i-1}+
       {if i+1<k then T.n+i+1 else s.1.2})+
      ({T.n+k+i}+{T.n+k+i}) := by
  have hk : k ≠ 0 := by omega
  have hold : edgeListNeighbors ((T.bonds.erase s.1).erase s.2) (T.n+i)=0 := by
    apply edgeListNeighbors_zero
    intro p hp
    have hh := erase_bonds_bounded _ s.2 T.n (erase_bonds_bounded _ s.1 T.n hT) p hp
    constructor <;> omega
  have hother : edgeListNeighbors
      (railBonds s.2.1 ((List.range k).map (T.n+k+·)) s.2.2) (T.n+i)=0 := by
    apply rail_neighbors_zero
    · omega
    · omega
    · intro w hw
      obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hw
      omega
  simp only [insertRungs,hk,ite_false,edgeListNeighbors_append,hold,hother,
    zero_add,add_zero,← allocatedRungs_eq_zip]
  rw [rail_allocated_neighbors T.n s.1.1 s.1.2 k i hs.1 hs.2.1 hi,
    allocatedRungs_neighbors_left T.n (T.n+k) k i (by omega) hi]

/-- Fresh right-rail vertex, with its two rail neighbors and doubled partner. -/
theorem insertRungs_neighbors_right (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k i : ℕ) (hi : i<k)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n) :
    edgeListNeighbors (insertRungs T s k).bonds (T.n+k+i)=
      ({if i=0 then s.2.1 else T.n+k+i-1}+
       {if i+1<k then T.n+k+i+1 else s.2.2})+
      ({T.n+i}+{T.n+i}) := by
  have hk : k ≠ 0 := by omega
  have hold : edgeListNeighbors ((T.bonds.erase s.1).erase s.2) (T.n+k+i)=0 := by
    apply edgeListNeighbors_zero
    intro p hp
    have hh := erase_bonds_bounded _ s.2 T.n (erase_bonds_bounded _ s.1 T.n hT) p hp
    constructor <;> omega
  have hother : edgeListNeighbors
      (railBonds s.1.1 ((List.range k).map (T.n+·)) s.1.2) (T.n+k+i)=0 := by
    apply rail_neighbors_zero
    · omega
    · omega
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
      have := List.mem_range.mp hj
      omega
  simp only [insertRungs,hk,ite_false,edgeListNeighbors_append,hold,hother,
    zero_add,← allocatedRungs_eq_zip]
  rw [rail_allocated_neighbors (T.n+k) s.2.1 s.2.2 k i (by omega) (by omega) hi,
    allocatedRungs_neighbors_right T.n (T.n+k) k i (by omega) hi]

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchRank
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Cells
import Mathlib.Tactic

/-! # Cells of the contracted molecule of a pinch

The new atom `none` has degree two, so it lies in no cell; between atoms of `Y` the contracted molecule has the bonds
of `N`. Hence its cells are the cells of `N` inside `Y`, with the same gaps.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

theorem aux_ends_of_mem {z : MoleProp.DeletedDart N T.Y} (h1 : N.atom z.val ∈ T.Y)
    (h2 : N.atom (N.mate z.val) ∈ T.Y) :
    T.aux.ends z = s(some (N.atom z.val), some (N.atom (N.mate z.val))) := by
  change s(T.aux.atom z, T.aux.atom (T.aux.mate z)) = _
  have e2 : T.aux.atom (T.aux.mate z) = some (N.atom (N.mate z.val)) :=
    (T.aux_atom_some (z := T.aux.mate z)).mpr ⟨rfl, h2⟩
  rw [T.aux_atom_some.mpr ⟨rfl, h1⟩, e2]

/-- Bonds between atoms of `Y` are those of `N`. -/
theorem aux_bondsBetween {a b : V} (ha : a ∈ T.Y) (hb : b ∈ T.Y) :
    T.aux.bondsBetween (some a) (some b) = N.bondsBetween a b := by
  classical
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter, filter_filter]
  refine card_bij (fun z _ => z.val) ?_ ?_ ?_
  · intro z hz
    obtain ⟨hout, hends⟩ := (mem_filter.mp hz).2
    refine mem_filter.mpr ⟨mem_univ _, hout, ?_⟩
    change s(T.aux.atom z, T.aux.atom (T.aux.mate z)) = s(some a, some b) at hends
    change s(N.atom z.val, N.atom (N.mate z.val)) = s(a, b)
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : N.atom z.val = a := (T.aux_atom_some.mp h1).1
      have e2 : N.atom (N.mate z.val) = b := (T.aux_atom_some.mp h2).1
      rw [e1, e2]
    · have e1 : N.atom z.val = b := (T.aux_atom_some.mp h1).1
      have e2 : N.atom (N.mate z.val) = a := (T.aux_atom_some.mp h2).1
      rw [e1, e2]; exact Sym2.eq_swap
  · intro z₁ _ z₂ _ h; exact Subtype.ext h
  · intro z hz
    obtain ⟨hout, hends⟩ := (mem_filter.mp hz).2
    change s(N.atom z, N.atom (N.mate z)) = s(a, b) at hends
    have hboth : N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y := by
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ ha, h2 ▸ hb⟩
      · exact ⟨h1 ▸ hb, h2 ▸ ha⟩
    have hzd : ¬(N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := fun h => h.1 hboth.1
    refine ⟨⟨z, hzd⟩, mem_filter.mpr ⟨mem_univ _, hout, ?_⟩, rfl⟩
    rw [T.aux_ends_of_mem hboth.1 hboth.2]
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact Sym2.eq_swap

/-- Directions between atoms of `Y` are those of `N`. -/
theorem aux_directed_iff {a b : V} (ha : a ∈ T.Y) (hb : b ∈ T.Y) :
    T.aux.Directed (some a) (some b) ↔ N.Directed a b := by
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    exact ⟨z.val, hz, (T.aux_atom_some.mp h1).1, (T.aux_atom_some.mp h2).1⟩
  · rintro ⟨z, hz, h1, h2⟩
    have hzY : N.atom z ∈ T.Y := h1 ▸ ha
    exact ⟨⟨z, fun h => h.1 hzY⟩, hz, T.aux_atom_some.mpr ⟨h1, ha⟩, T.aux_atom_some.mpr ⟨h2, hb⟩⟩

theorem aux_loop_free (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    ∀ z, T.aux.atom z ≠ T.aux.atom (T.aux.mate z) := by
  intro z h
  by_cases h1 : N.atom z.val ∈ T.Y
  · have e1 := T.aux_atom_some.mpr ⟨rfl, h1⟩
    rw [e1] at h
    have := (T.aux_atom_some (z := T.aux.mate z)).mp h.symm
    exact hloop z.val this.1.symm
  · have e1 := T.aux_atom_none.mpr h1
    rw [e1] at h
    have := (T.aux_atom_none (z := T.aux.mate z)).mp h.symm
    exact z.property ⟨h1, this⟩

/-- The new atom lies in no cell. -/
theorem none_notMem_cell (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {S : Finset (Option V)}
    (hS : S ∈ MoleProp.ladderCells T.aux) : none ∉ S := by
  classical
  intro hn
  obtain ⟨_, u, v, hL, rfl⟩ := mem_filter.mp hS
  obtain ⟨p, q, _, hp, hq, _, _⟩ := cell_quad hL hn
  have hl := T.aux_loop_free hloop
  have hnp : (none : Option V) ≠ p := by
    intro h; rw [← h, bondsBetween_self_eq_zero hl] at hp; omega
  have hnq : (none : Option V) ≠ q := by
    intro h; rw [← h, bondsBetween_self_eq_zero hl] at hq; omega
  have hpq : p ≠ q := by intro h; rw [h] at hp; omega
  have hs := Degen.sum_neighbor_bonds_le_degree T.aux none {p, q} (by simp [hnp, hnq])
  rw [sum_pair hpq, hp, hq, T.aux_deg_none] at hs
  omega

/-- The scale function transported to the contracted molecule. -/
noncomputable def auxScale (P : Finset V → ℝ) (S : Finset (Option V)) : ℝ :=
  P (S.preimage some (Option.some_injective V).injOn)

theorem preimage_image_some (S : Finset V) :
    (S.image some).preimage some (Option.some_injective V).injOn = S := by
  ext v; simp

end Pinch
end WaveTurbulence.MoleProp4

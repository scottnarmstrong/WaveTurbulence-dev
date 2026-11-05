/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
/-! A partition into nonempty irreducible closed blocks is unique when closure is intersection-stable. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem finpartition_eq_of_irreducible_closed_blocks {α : Type*} [DecidableEq α]
    {U : Finset α} (P Q : Finpartition U) (Closed : Finset α → Prop)
    (hinter : ∀ A B, Closed A → Closed B → Closed (A ∩ B))
    (hP : ∀ B ∈ P.parts, Closed B ∧ ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ Closed A)
    (hQ : ∀ B ∈ Q.parts, Closed B ∧ ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ Closed A) : P = Q := by
  have hblock {B C : Finset α} (hB : B ∈ P.parts) (hC : C ∈ Q.parts)
      {x : α} (hxB : x ∈ B) (hxC : x ∈ C) : B = C := by
    have hc := hinter B C (hP B hB).1 (hQ C hC).1
    have hn : (B ∩ C).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hxB, hxC⟩⟩
    have heB : B ∩ C = B := by
      by_contra hne
      exact (hP B hB).2 _ (Finset.inter_subset_left) hn hne hc
    have heC : B ∩ C = C := by
      by_contra hne
      exact (hQ C hC).2 _ (Finset.inter_subset_right) hn hne hc
    exact heB.symm.trans heC
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    have hxU := P.le hB hx
    have he := hblock hB (Q.part_mem.mpr hxU) hx (Q.mem_part hxU)
    exact he.symm ▸ Q.part_mem.mpr hxU
  · intro hB
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
    have hxU := Q.le hB hx
    have he := hblock (P.part_mem.mpr hxU) hB (P.mem_part hxU) hx
    exact he ▸ P.part_mem.mpr hxU

end WaveTurbulence.Induct

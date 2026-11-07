/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideLinks
import Mathlib.Tactic

/-! # Exact factorization of ladder-link weights over closed sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem links_closed_side_union (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    appbLinks M = appbLinks (appbSideMolecule M S hS) ∪
      appbLinks (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  classical
  ext T
  simp only [mem_union,mem_appbLinks,link_closed_side_iff]
  constructor
  · intro hT
    rcases link_subset_one_closed_side M S hS hT with h | h
    · exact Or.inl ⟨hT,h⟩
    · exact Or.inr ⟨hT,h⟩
  · rintro (⟨hT,h⟩ | ⟨hT,h⟩) <;> exact hT

theorem links_closed_side_disjoint (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    Disjoint (appbLinks (appbSideMolecule M S hS))
      (appbLinks (appbSideMolecule M (M.atoms \ S) hS.complement)) := by
  classical
  apply disjoint_left.mpr
  intro T hT hT'
  obtain ⟨h,hs⟩ := (link_closed_side_iff M S hS T).mp ((mem_appbLinks _ _).mp hT)
  have ht := ((link_closed_side_iff M (M.atoms \ S) hS.complement T).mp
    ((mem_appbLinks _ _).mp hT')).2
  have hnon : T.Nonempty := card_pos.mp (by rw [h.card]; decide)
  obtain ⟨a,ha⟩ := hnon
  exact (mem_sdiff.mp (ht ha)).2 (hs ha)

/-- There is no loss and no positivity assumption on the prescribed
scales: this is a literal disjoint partition of the actual link family. -/
theorem linkProduct_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct M L γ δ P =
      appbLinkProduct (appbSideMolecule M S hS) L γ δ P*
        appbLinkProduct (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ P := by
  unfold appbLinkProduct
  rw [links_closed_side_union M S hS,prod_union (links_closed_side_disjoint M S hS)]

end WaveTurbulence.Mole.AppbAlgorithm

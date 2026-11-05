/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # Standalone ladder atom counts (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The two rails of an actual ladder have disjoint atom sets. -/
theorem ladder_rails_disjoint {M : Molecule V D} {m : ℕ} {u v : Fin (m+1) → V}
    (h : M.IsLadder u v) : Disjoint (univ.image u) (univ.image v) := by
  apply disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,_hi,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_hj,hj⟩ := mem_image.mp hb
  have he := h.2.1 (show Sum.elim u v (.inl i) = Sum.elim u v (.inr j) from hj.symm)
  cases he

/-- A standalone length-m ladder has exactly 2(m+1) atoms. -/
theorem ladder_card {M : Molecule V D} {m : ℕ} {u v : Fin (m+1) → V}
    (h : M.IsLadder u v) : (Molecule.ladderAtoms u v).card = 2*(m+1) := by
  have hu : Function.Injective u := fun i j he => Sum.inl.inj (h.2.1 he)
  have hv : Function.Injective v := fun i j he => Sum.inr.inj (h.2.1 he)
  rw [Molecule.ladderAtoms,card_union_of_disjoint (ladder_rails_disjoint h),
    card_image_of_injective _ hu,card_image_of_injective _ hv]
  simp only [card_univ,Fintype.card_fin]
  omega

/-- The draft atom-set definition of length agrees with the actual length. -/
theorem ladderLength_eq {M : Molecule V D} {m : ℕ} {u v : Fin (m+1) → V}
    (h : M.IsLadder u v) : Molecule.ladderLength (Molecule.ladderAtoms u v) = m := by
  rw [Molecule.ladderLength,ladder_card h]
  omega

end WaveTurbulence.Vine

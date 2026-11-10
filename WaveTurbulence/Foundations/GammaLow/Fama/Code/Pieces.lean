/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.TVine.Defs
import Mathlib.Tactic
/-! # The pieces of an atomic group partition its interior (packet L5a, item H)

D11's `Molecule.pieces S j₁ j₂` is the image of the `SamePiece`-class map on `S ∖ {j₁, j₂}`. `SamePiece` is an
equivalence (it is an intersection of path-connectivity relations), so the pieces are pairwise disjoint, nonempty,
contained in the interior, and cover it. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama.ClassCount
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem samePiece_refl (S : Finset V) (u : V) : M.SamePiece S u u := fun _ _ _ => Relation.EqvGen.refl _

theorem samePiece_symm {S : Finset V} {u w : V} (h : M.SamePiece S u w) : M.SamePiece S w u :=
  fun F h1 h2 => Relation.EqvGen.symm _ _ (h F h1 h2)

theorem samePiece_trans {S : Finset V} {u v w : V} (h₁ : M.SamePiece S u v) (h₂ : M.SamePiece S v w) :
    M.SamePiece S u w :=
  fun F h1 h2 => Relation.EqvGen.trans _ _ _ (h₁ F h1 h2) (h₂ F h1 h2)

/-- Membership in a piece. -/
theorem mem_pieces_iff {S : Finset V} {j₁ j₂ : V} {P : Finset V} :
    P ∈ M.pieces S j₁ j₂ ↔ ∃ u ∈ (S.erase j₁).erase j₂, ∀ w, w ∈ P ↔ w ∈ (S.erase j₁).erase j₂ ∧ M.SamePiece S u w := by
  classical
  unfold Molecule.pieces
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, fun w => by simp [Finset.mem_filter]⟩
  · rintro ⟨u, hu, hP⟩
    refine ⟨u, hu, ?_⟩
    ext w
    rw [hP w]
    simp [Finset.mem_filter]

theorem pieces_subset {S : Finset V} {j₁ j₂ : V} {P : Finset V} (hP : P ∈ M.pieces S j₁ j₂) :
    P ⊆ (S.erase j₁).erase j₂ := by
  obtain ⟨u, -, h⟩ := (mem_pieces_iff M).mp hP
  exact fun w hw => ((h w).mp hw).1

/-- Two pieces sharing an atom are equal. -/
theorem piece_eq_of_mem {S : Finset V} {j₁ j₂ : V} {P Q : Finset V} (hP : P ∈ M.pieces S j₁ j₂)
    (hQ : Q ∈ M.pieces S j₁ j₂) {z : V} (hzP : z ∈ P) (hzQ : z ∈ Q) : P = Q := by
  obtain ⟨u, -, hu⟩ := (mem_pieces_iff M).mp hP
  obtain ⟨v, -, hv⟩ := (mem_pieces_iff M).mp hQ
  have h1 := ((hu z).mp hzP).2
  have h2 := ((hv z).mp hzQ).2
  have huv : M.SamePiece S u v := samePiece_trans M h1 (samePiece_symm M h2)
  ext w
  rw [hu w, hv w]
  exact ⟨fun ⟨h, h'⟩ => ⟨h, samePiece_trans M (samePiece_symm M huv) h'⟩,
    fun ⟨h, h'⟩ => ⟨h, samePiece_trans M huv h'⟩⟩

end WaveTurbulence.GammaLow.Fama.ClassCount

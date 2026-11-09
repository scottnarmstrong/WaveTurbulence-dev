/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Inputs
public import WaveTurbulence.Foundations.TVine.Chart.Bonds

/-!
# Derivation of the cell decomposition, I: pieces, crossing bonds, bonds at an atom

Basic facts used to turn the piece structure (N3 Theorem 6, N2 Prop 1.17(b), M4 Lemma A, as stated by L3) into a
cell decomposition:
* the pieces (pinned `Molecule.pieces`) partition the interior `S ∖ {a, b}`;
* `cross A B`, the internal bonds with one end in `A` and the other in `B`, has `L3`'s `crossBonds M A B` elements;
* the bonds at an atom number at most its degree within `S`, so a family of that many distinct bonds at the atom
  is all of them (`bondsAt_eq_of_card`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}

/-! ## Pieces partition the interior -/

theorem samePiece_refl (u : V) : M.SamePiece S u u := fun _ _ _ => Relation.EqvGen.refl _

theorem samePiece_symm {u w : V} (h : M.SamePiece S u w) : M.SamePiece S w u :=
  fun F hF hc => Relation.EqvGen.symm _ _ (h F hF hc)

theorem samePiece_trans {u v w : V} (h₁ : M.SamePiece S u v) (h₂ : M.SamePiece S v w) : M.SamePiece S u w :=
  fun F hF hc => Relation.EqvGen.trans _ _ _ (h₁ F hF hc) (h₂ F hF hc)

open Classical in
theorem mem_pieces {a b : V} {P : Finset V} :
    P ∈ M.pieces S a b ↔ ∃ u ∈ (S.erase a).erase b, P = ((S.erase a).erase b).filter fun w => M.SamePiece S u w := by
  classical
  unfold Molecule.pieces
  simp only [mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by congr⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by congr⟩

open Classical in
theorem pieces_sub {a b : V} {P : Finset V} (hP : P ∈ M.pieces S a b) : P ⊆ (S.erase a).erase b := by
  obtain ⟨u, -, rfl⟩ := mem_pieces.mp hP
  exact filter_subset _ _

open Classical in
theorem pieces_disjoint {a b : V} {P Q : Finset V} (hP : P ∈ M.pieces S a b) (hQ : Q ∈ M.pieces S a b)
    {v : V} (hvP : v ∈ P) (hvQ : v ∈ Q) : P = Q := by
  obtain ⟨u, hu, hPu⟩ := mem_pieces.mp hP
  obtain ⟨u', hu', hQu⟩ := mem_pieces.mp hQ
  rw [hPu] at hvP ⊢
  rw [hQu] at hvQ ⊢
  have h1 := (mem_filter.mp hvP).2
  have h2 := (mem_filter.mp hvQ).2
  have h12 : M.SamePiece S u u' := samePiece_trans h1 (samePiece_symm h2)
  ext w
  simp only [mem_filter]
  exact ⟨fun ⟨hw, h⟩ => ⟨hw, samePiece_trans (samePiece_symm h12) h⟩,
    fun ⟨hw, h⟩ => ⟨hw, samePiece_trans h12 h⟩⟩

open Classical in
theorem pieces_cover {a b v : V} (hv : v ∈ S) (ha : v ≠ a) (hb : v ≠ b) : ∃ P ∈ M.pieces S a b, v ∈ P := by
  have hvi : v ∈ (S.erase a).erase b := mem_erase.mpr ⟨hb, mem_erase.mpr ⟨ha, hv⟩⟩
  exact ⟨_, mem_pieces.mpr ⟨v, hvi, rfl⟩, mem_filter.mpr ⟨hvi, samePiece_refl v⟩⟩

/-! ## Crossing bonds -/

/-- The internal bonds with one end in `A` and the other in `B`. -/
noncomputable def cross (A B : Finset V) : Finset (Bond M S) :=
  univ.filter fun e : Bond M S => (tl e ∈ A ∧ hd e ∈ B) ∨ (tl e ∈ B ∧ hd e ∈ A)

theorem mem_cross {A B : Finset V} {e : Bond M S} :
    e ∈ cross A B ↔ (tl e ∈ A ∧ hd e ∈ B) ∨ (tl e ∈ B ∧ hd e ∈ A) := by
  simp [cross]

theorem card_cross {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) :
    (cross (M := M) (S := S) A B).card = Struct.crossBonds M A B := by
  classical
  unfold Struct.crossBonds
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    rw [mem_cross] at he
    simp only [Molecule.bonds, mem_filter, mem_univ, true_and]
    exact ⟨(bond_spec e).1, he⟩
  · intro e _ f _ h; exact Subtype.ext h
  · intro x hx
    simp only [Molecule.bonds, mem_filter, mem_univ, true_and] at hx
    have hS : M.InGroup S x := by
      rcases hx.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hA h1, hB h2⟩
      · exact ⟨hB h1, hA h2⟩
    exact ⟨⟨x, mem_internalBondSet hx.1 hS⟩, mem_cross.mpr hx.2, rfl⟩

theorem cross_comm (A B : Finset V) : cross (M := M) (S := S) A B = cross B A := by
  ext e; simp only [mem_cross]; tauto

theorem cross_eq_empty_of {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) (h : Struct.crossBonds M A B = 0) :
    cross (M := M) (S := S) A B = ∅ := by
  rw [← Finset.card_eq_zero, card_cross hA hB, h]

theorem not_cross_of_zero {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) (h : Struct.crossBonds M A B = 0)
    {e : Bond M S} (he1 : tl e ∈ A) (he2 : hd e ∈ B) : False := by
  have := cross_eq_empty_of (M := M) hA hB h
  have hm : e ∈ cross (M := M) (S := S) A B := mem_cross.mpr (Or.inl ⟨he1, he2⟩)
  rw [this] at hm; exact absurd hm (Finset.notMem_empty _)

/-! ## Bonds at an atom -/

/-- The internal bonds at an atom. -/
noncomputable def bondsAt (v : V) : Finset (Bond M S) := univ.filter fun e : Bond M S => tl e = v ∨ hd e = v

theorem mem_bondsAt {v : V} {e : Bond M S} : e ∈ bondsAt v ↔ tl e = v ∨ hd e = v := by simp [bondsAt]

theorem card_bondsAt_le (v : V) : (bondsAt (M := M) (S := S) v).card ≤ M.degIn S v := by
  classical
  have : bondsAt (M := M) (S := S) v = (univ.filter fun e => tl e = v) ∪ (univ.filter fun e => hd e = v) := by
    ext e; simp [bondsAt]
  rw [this, degIn_eq, ← card_tl, ← card_hd]
  exact card_union_le _ _

/-- A family of `degIn` distinct bonds at `v` is all the bonds at `v`. -/
theorem bondsAt_eq_of_card {v : V} (T : Finset (Bond M S)) (hT : T ⊆ bondsAt v) (hc : M.degIn S v ≤ T.card) :
    T = bondsAt v :=
  Finset.eq_of_subset_of_card_le hT (le_trans (card_bondsAt_le v) hc)

end WaveTurbulence.TVine.Chart

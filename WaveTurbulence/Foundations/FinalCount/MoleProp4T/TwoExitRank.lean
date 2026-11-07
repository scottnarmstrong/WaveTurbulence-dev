/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitPost
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-! # Circuit ranks around a two-exit removal

`χ(N) − χ(post) − χ(N[Y]) = F(N) − F(post) ≥ 0` when `N[Y]` is connected: the bonds of `N` are those of the piece,
those of the rest and the two exits, and the post molecule has the bonds of the rest and the new bond. Every
component of the post molecule lies in one of `N` and distinct ones in distinct ones (`fold` sends `Y` to `c`). This is
DH23's "`Δχ = −2n`" (L1954) with the removed piece accounted separately.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- If `g u = g v` forces `f u = f v` on `s`, then `f` has at most as many values as `g`. -/
theorem card_image_le_of_factor {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α) (f : α → β)
    (g : α → γ) (h : ∀ u ∈ s, ∀ v ∈ s, g u = g v → f u = f v) : (s.image f).card ≤ (s.image g).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have ih' := ih fun u hu v hv => h u (mem_insert_of_mem hu) v (mem_insert_of_mem hv)
    rw [image_insert, image_insert]
    by_cases hg : g a ∈ t.image g
    · obtain ⟨b, hb, hba⟩ := mem_image.mp hg
      have hf : f a ∈ t.image f :=
        mem_image.mpr ⟨b, hb, h b (mem_insert_of_mem hb) a (mem_insert_self a t) hba⟩
      rw [insert_eq_of_mem hf, insert_eq_of_mem hg]; exact ih'
    · rw [card_insert_of_notMem hg]
      exact (card_insert_le _ _).trans (by omega)

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **Dart count**: darts of `N` = darts of the piece + darts of the rest + the four exit darts. -/
theorem card_darts :
    Fintype.card D = Fintype.card (Degen.RetainedDart N (N.atoms \ T.Y)) +
      Fintype.card (Degen.RetainedDart N T.Y) + 4 := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hin : (univ.filter fun z : D => N.atom z ∉ N.atoms \ T.Y ∧ N.atom (N.mate z) ∉ N.atoms \ T.Y) =
      univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y := by
    ext z; simp only [mem_filter, mem_univ, true_and, mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 (N.atom_mem _), h2 (N.atom_mem _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩
  rw [hin]
  have hex : ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D).card = 4 := by
    have hxy := T.ne
    have hmm := T.mate_x_ne_mate_y
    have h1 : T.x ≠ N.mate T.x := fun h => (N.mate_ne T.x) h.symm
    have h2 : T.x ≠ N.mate T.y := by
      intro h; have := T.atom_x; rw [h] at this; exact T.d_notMem this
    have h3 : T.y ≠ N.mate T.x := by
      intro h; have := T.atom_y; rw [h] at this; exact T.c_notMem this
    have h4 : T.y ≠ N.mate T.y := fun h => (N.mate_ne T.y) h.symm
    rw [card_insert_of_notMem (by simp [hxy, h1, h2]), card_insert_of_notMem (by simp [h3, h4]),
      card_insert_of_notMem (by simp [hmm]), card_singleton]
  have hpart : (univ : Finset D) = (univ.filter fun z => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∪ {T.x, T.y, N.mate T.x, N.mate T.y} := by
    ext z
    simp only [mem_univ, mem_union, mem_filter, true_and, mem_insert, mem_singleton, true_iff]
    rcases T.dart_cases z with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    all_goals right; tauto
  have hd1 : Disjoint (univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y)
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    rw [disjoint_filter]; intro z _ h h'; exact h'.1 h.1
  have hex_not : ∀ z ∈ ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D),
      ¬(N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∧ ¬(N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨fun h => T.c_notMem h.2, fun h => h.1 T.atom_x⟩
    · exact ⟨fun h => T.d_notMem h.2, fun h => h.1 T.atom_y⟩
    · rw [N.mate_mate]; exact ⟨fun h => T.c_notMem h.1, fun h => h.2 T.atom_x⟩
    · rw [N.mate_mate]; exact ⟨fun h => T.d_notMem h.1, fun h => h.2 T.atom_y⟩
  have hd2 : Disjoint ((univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y)) {T.x, T.y, N.mate T.x, N.mate T.y} := by
    rw [disjoint_right]
    intro z hz hzf
    rcases mem_union.mp hzf with h | h
    · exact (hex_not z hz).1 (mem_filter.mp h).2
    · exact (hex_not z hz).2 (mem_filter.mp h).2
  have htot := congrArg Finset.card hpart
  rw [← card_univ, htot, card_union_of_disjoint hd2, card_union_of_disjoint hd1, hex]

theorem card_post_darts : Fintype.card (Degen.RetainedDart N T.Y ⊕ Bool) = Fintype.card (Degen.RetainedDart N T.Y) + 2 := by
  rw [Fintype.card_sum, Fintype.card_bool]

theorem bonds_eq : N.bonds.card = (piece N T.Y).bonds.card + (Degen.eraseAtoms N T.Y).bonds.card + 2 := by
  have h1 := Mole.two_mul_card_bonds N
  have h2 := Mole.two_mul_card_bonds (piece N T.Y)
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_darts
  omega

theorem post_bonds_eq : T.post.bonds.card = (Degen.eraseAtoms N T.Y).bonds.card + 1 := by
  have h1 := Mole.two_mul_card_bonds T.post
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_post_darts
  omega

theorem atoms_card : N.atoms.card = T.Y.card + (N.atoms \ T.Y).card := by
  rw [card_sdiff_of_subset T.sub]; have := card_le_card T.sub; omega

/-- `fold` sends `Y` to `c`: adjacency in `N` becomes connectivity in the post molecule. -/
theorem post_sameComponent_fold {u v : V} (h : N.SameComponent u v) :
    T.post.SameComponent (if u ∈ T.Y then T.c else u) (if v ∈ T.Y then T.c else v) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hcY : N.atom (N.mate T.x) ∉ T.Y := T.c_notMem
    have hdY : N.atom (N.mate T.y) ∉ T.Y := T.d_notMem
    rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
    · simp only [h.1, h.2, ite_true]; exact Relation.EqvGen.refl _
    · simp only [h.1, h.2, ite_false]
      exact Relation.EqvGen.rel _ _ ⟨Sum.inl ⟨z, h.1, h.2⟩, rfl, rfl⟩
    · simp only [T.atom_x, hcY, ite_true, ite_false]; exact Relation.EqvGen.refl _
    · simp only [T.atom_y, hdY, ite_true, ite_false]
      exact Relation.EqvGen.rel _ _ ⟨Sum.inr false, rfl, rfl⟩
    · simp only [N.mate_mate, T.atom_x, hcY, ite_true, ite_false]; exact Relation.EqvGen.refl _
    · simp only [N.mate_mate, T.atom_y, hdY, ite_true, ite_false]
      exact Relation.EqvGen.rel _ _ ⟨Sum.inr true, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b e _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **`F(post) ≤ F(N)`.** -/
theorem post_numComponents_le : T.post.numComponents ≤ N.numComponents := by
  classical
  rw [Degen.numComponents_eq_card_componentSets, Degen.numComponents_eq_card_componentSets]
  unfold Degen.componentSets
  rw [T.post_atoms]
  refine (card_image_le_of_factor (N.atoms \ T.Y) (Degen.componentSet T.post) (Degen.componentSet N) ?_).trans
    (card_le_card (image_subset_image sdiff_subset))
  intro u hu v hv he
  obtain ⟨huN, huY⟩ := mem_sdiff.mp hu
  obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
  have hs := (Degen.componentSet_eq_iff N huN).mp he
  have hf := T.post_sameComponent_fold hs
  simp only [huY, hvY, ite_false] at hf
  have hu' : u ∈ T.post.atoms := by rw [T.post_atoms]; exact hu
  exact (Degen.componentSet_eq_iff T.post hu').mpr hf

/-- **Circuit ranks**: `χ(N) − χ(post) − χ(N[Y]) = F(N) − F(post) − F(N[Y]) + 1`. -/
theorem circuitRank_identity :
    N.circuitRank - T.post.circuitRank - (piece N T.Y).circuitRank =
      (N.numComponents : ℤ) - T.post.numComponents - (piece N T.Y).numComponents + 1 := by
  unfold Molecule.circuitRank
  rw [T.bonds_eq, T.post_bonds_eq, T.atoms_card, T.post_atoms, piece_atoms T.sub]
  push_cast
  ring

end TwoExit
end WaveTurbulence.MoleProp4

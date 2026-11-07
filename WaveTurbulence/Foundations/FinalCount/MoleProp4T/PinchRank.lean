/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchGraph
import Mathlib.Tactic

/-! # The contracted molecule of a pinch: connectivity, molecule axioms and circuit ranks -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

theorem aux_deg_none : T.aux.deg none = 2 := by
  unfold Molecule.deg; rw [T.aux_dartsAt_none, card_pair]
  intro h; exact T.mate_x_ne_mate_y (congrArg Subtype.val h)

theorem none_mem : (none : Option V) ∈ T.aux.atoms := mem_insert_self _ _

theorem some_mem {v : V} (hv : v ∈ T.Y) : some v ∈ T.aux.atoms := mem_insert_of_mem (mem_image_of_mem _ hv)

theorem mem_aux_atoms {o : Option V} : o ∈ T.aux.atoms ↔ o = none ∨ ∃ v ∈ T.Y, o = some v := by
  change o ∈ insert none (T.Y.image some) ↔ _
  simp only [mem_insert, mem_image]
  constructor
  · rintro (h | ⟨v, hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (h | ⟨v, hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, rfl⟩

theorem aux_sameComponent_some {u v : V} (h : (piece N T.Y).SameComponent u v) :
    T.aux.SameComponent (some u) (some v) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hz := piece_dart_mem z
    refine Relation.EqvGen.rel _ _ ⟨⟨z.val, fun h => h.1 hz.1⟩, ?_, ?_⟩
    · exact T.aux_atom_some.mpr ⟨rfl, hz.1⟩
    · exact T.aux_atom_some.mpr ⟨rfl, hz.2⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem aux_connected (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) :
    ∀ o ∈ T.aux.atoms, T.aux.SameComponent o none := by
  have hx : T.aux.SameComponent (some (N.atom T.x)) none := by
    refine Relation.EqvGen.rel _ _ ⟨⟨T.x, fun h => h.1 T.atom_x⟩, T.aux_atom_some.mpr ⟨rfl, T.atom_x⟩, ?_⟩
    exact T.aux_atom_none.mpr T.w_notMem
  intro o ho
  rcases T.mem_aux_atoms.mp ho with rfl | ⟨v, hv, rfl⟩
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _ (T.aux_sameComponent_some (hconn v hv _ T.atom_x)) hx

/-- `aux` is a molecule. -/
theorem aux_isMolecule (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) : T.aux.IsMolecule :=
  ⟨T.aux_caps hcap, fun o ho => ⟨none, T.none_mem, T.aux_connected hconn o ho, by rw [T.aux_deg_none]; norm_num⟩⟩

theorem aux_numComponents (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) :
    T.aux.numComponents = 1 :=
  Mole.numComponents_eq_one T.aux ⟨none, T.none_mem⟩ fun u hu v hv =>
    Relation.EqvGen.trans _ _ _ (T.aux_connected hconn u hu)
      (Relation.EqvGen.symm _ _ (T.aux_connected hconn v hv))

theorem aux_atoms_card : T.aux.atoms.card = T.Y.card + 1 := by
  change (insert none (T.Y.image some)).card = _
  rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective V)]

/-- Every dart is inside `Y`, outside `Y`, or an exit dart. -/
theorem dart_cases (z : D) :
    (N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∨ (N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∨
      z = T.x ∨ z = T.y ∨ z = N.mate T.x ∨ z = N.mate T.y := by
  have hcr : ∀ z, N.atom z ∈ T.Y → N.atom (N.mate z) ∉ T.Y → z = T.x ∨ z = T.y := by
    intro z h1 h2
    have hz : z ∈ crossDarts N T.Y := mem_crossDarts.mpr ⟨h1, h2⟩
    rw [T.cross] at hz; simpa using hz
  by_cases h1 : N.atom z ∈ T.Y <;> by_cases h2 : N.atom (N.mate z) ∈ T.Y
  · exact Or.inl ⟨h1, h2⟩
  · rcases hcr z h1 h2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hcr (N.mate z) h2 (by rw [N.mate_mate]; exact h1) with h | h
    · right; right; right; right; left; rw [← h, N.mate_mate]
    · right; right; right; right; right; rw [← h, N.mate_mate]
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- Darts: those of the piece, of the rest, and the four exit darts. -/
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
  have hwY : N.atom (N.mate T.x) ∉ T.Y := T.w_notMem
  have hwY' : N.atom (N.mate T.y) ∉ T.Y := by rw [← T.same]; exact T.w_notMem
  have hex : ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D).card = 4 := by
    have h1 : T.x ≠ N.mate T.x := fun h => (N.mate_ne T.x) h.symm
    have h2 : T.x ≠ N.mate T.y := by intro h; have := T.atom_x; rw [h] at this; exact hwY' this
    have h3 : T.y ≠ N.mate T.x := by intro h; have := T.atom_y; rw [h] at this; exact hwY this
    have h4 : T.y ≠ N.mate T.y := fun h => (N.mate_ne T.y) h.symm
    rw [card_insert_of_notMem (by simp [T.ne, h1, h2]), card_insert_of_notMem (by simp [h3, h4]),
      card_insert_of_notMem (by simp [T.mate_x_ne_mate_y]), card_singleton]
  have hex_not : ∀ z ∈ ({T.x, T.y, N.mate T.x, N.mate T.y} : Finset D),
      ¬(N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∧ ¬(N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨fun h => hwY h.2, fun h => h.1 T.atom_x⟩
    · exact ⟨fun h => hwY' h.2, fun h => h.1 T.atom_y⟩
    · rw [N.mate_mate]; exact ⟨fun h => hwY h.1, fun h => h.2 T.atom_x⟩
    · rw [N.mate_mate]; exact ⟨fun h => hwY' h.1, fun h => h.2 T.atom_y⟩
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
  have hd2 : Disjoint ((univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y)) {T.x, T.y, N.mate T.x, N.mate T.y} := by
    rw [disjoint_right]
    intro z hz hzf
    rcases mem_union.mp hzf with h | h
    · exact (hex_not z hz).1 (mem_filter.mp h).2
    · exact (hex_not z hz).2 (mem_filter.mp h).2
  have htot := congrArg Finset.card hpart
  rw [← card_univ, htot, card_union_of_disjoint hd2, card_union_of_disjoint hd1, hex]

theorem card_aux_darts :
    Fintype.card (MoleProp.DeletedDart N T.Y) = Fintype.card (Degen.RetainedDart N (N.atoms \ T.Y)) + 4 := by
  have h := T.card_darts
  have hc : Fintype.card (MoleProp.DeletedDart N T.Y) + Fintype.card (Degen.RetainedDart N T.Y) =
      Fintype.card D := by
    classical
    rw [Fintype.card_subtype, Fintype.card_subtype, add_comm, card_filter_add_card_filter_not, card_univ]
  omega

theorem bonds_eq : N.bonds.card = (piece N T.Y).bonds.card + (Degen.eraseAtoms N T.Y).bonds.card + 2 := by
  have h1 := Mole.two_mul_card_bonds N
  have h2 := Mole.two_mul_card_bonds (piece N T.Y)
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_darts
  omega

theorem aux_bonds_eq : T.aux.bonds.card = (piece N T.Y).bonds.card + 2 := by
  have h1 := Mole.two_mul_card_bonds T.aux
  have h2 := Mole.two_mul_card_bonds (piece N T.Y)
  have h4 := T.card_aux_darts
  omega

/-- Folding `Y` onto `w`. -/
theorem erase_sameComponent_fold {u v : V} (h : N.SameComponent u v) :
    (Degen.eraseAtoms N T.Y).SameComponent (if u ∈ T.Y then T.w else u) (if v ∈ T.Y then T.w else v) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hwY : N.atom (N.mate T.x) ∉ T.Y := T.w_notMem
    have hwY' : N.atom (N.mate T.y) ∉ T.Y := by rw [← T.same]; exact T.w_notMem
    rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
    · simp only [h.1, h.2, ite_true]; exact Relation.EqvGen.refl _
    · simp only [h.1, h.2, ite_false]
      exact Relation.EqvGen.rel _ _ ⟨⟨z, h.1, h.2⟩, rfl, rfl⟩
    · simp only [T.atom_x, hwY, ite_true, ite_false]; exact Relation.EqvGen.refl _
    · simp only [T.atom_y, hwY', ite_true, ite_false]; rw [show N.atom (N.mate T.y) = T.w from T.same.symm]
      exact Relation.EqvGen.refl _
    · simp only [N.mate_mate, T.atom_x, hwY, ite_true, ite_false]; exact Relation.EqvGen.refl _
    · simp only [N.mate_mate, T.atom_y, hwY', ite_true, ite_false]; rw [show N.atom (N.mate T.y) = T.w from T.same.symm]
      exact Relation.EqvGen.refl _
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b e _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem erase_numComponents_le : (Degen.eraseAtoms N T.Y).numComponents ≤ N.numComponents := by
  classical
  rw [Degen.numComponents_eq_card_componentSets, Degen.numComponents_eq_card_componentSets]
  unfold Degen.componentSets
  change ((N.atoms \ T.Y).image (Degen.componentSet (Degen.eraseAtoms N T.Y))).card ≤ _
  refine (card_image_le_of_factor (N.atoms \ T.Y) (Degen.componentSet (Degen.eraseAtoms N T.Y))
    (Degen.componentSet N) ?_).trans (card_le_card (image_subset_image sdiff_subset))
  intro u hu v hv he
  obtain ⟨huN, huY⟩ := mem_sdiff.mp hu
  obtain ⟨_, hvY⟩ := mem_sdiff.mp hv
  have hs := (Degen.componentSet_eq_iff N huN).mp he
  have hf := T.erase_sameComponent_fold hs
  simp only [huY, hvY, ite_false] at hf
  exact (Degen.componentSet_eq_iff (Degen.eraseAtoms N T.Y) hu).mpr hf

/-- `χ(N) − χ(N ∖ Y) − χ(aux) = F(N) − F(N ∖ Y)`. -/
theorem circuitRank_identity (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) :
    N.circuitRank - (Degen.eraseAtoms N T.Y).circuitRank - T.aux.circuitRank =
      (N.numComponents : ℤ) - (Degen.eraseAtoms N T.Y).numComponents := by
  unfold Molecule.circuitRank
  have hat : N.atoms.card = T.Y.card + (N.atoms \ T.Y).card := by
    rw [card_sdiff_of_subset T.sub]; have := card_le_card T.sub; omega
  rw [T.bonds_eq, hat, T.aux_bonds_eq, T.aux_atoms_card, T.aux_numComponents hconn]
  change _ - (((Degen.eraseAtoms N T.Y).bonds.card : ℤ) - ((N.atoms \ T.Y).card : ℤ) + _) - _ = _
  push_cast
  ring

/-- `χ(aux) = |Y| + 1` when all atoms of `Y` have degree four. -/
theorem aux_circuitRank (hdegY : ∀ v ∈ T.Y, N.deg v = 4)
    (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) :
    T.aux.circuitRank = T.Y.card + 1 := by
  classical
  have hsum := Mole.sum_degrees_eq_two_mul_bonds (piece N T.Y)
  rw [piece_atoms T.sub] at hsum
  have hsplit : ∀ v ∈ T.Y, (piece N T.Y).deg v + (Degen.removedDartsAt N (N.atoms \ T.Y) v).card = 4 := by
    intro v hv
    rw [deg_eraseAtoms_add (N := N) (N.atoms \ T.Y) (fun h => (mem_sdiff.mp h).2 hv), hdegY v hv]
  have hcross : ∑ v ∈ T.Y, (Degen.removedDartsAt N (N.atoms \ T.Y) v).card = 2 := by
    have hfib := card_eq_sum_card_fiberwise (s := crossDarts N T.Y) (t := T.Y) (f := N.atom)
      (fun z hz => (mem_crossDarts.mp hz).1)
    rw [T.cross, card_pair T.ne] at hfib
    rw [hfib]
    refine sum_congr rfl fun v hv => congrArg card ?_
    ext z
    simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_sdiff]
    rw [← T.cross]
    simp only [mem_crossDarts]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨⟨hv, h.2⟩, rfl⟩
    · rintro ⟨⟨_, h⟩, rfl⟩; exact ⟨rfl, N.atom_mem _, h⟩
  have htot : ∑ v ∈ T.Y, (piece N T.Y).deg v + 2 = 4 * T.Y.card := by
    rw [← hcross, ← sum_add_distrib, sum_congr rfl hsplit, sum_const, smul_eq_mul, mul_comm]
  unfold Molecule.circuitRank
  rw [T.aux_bonds_eq, T.aux_atoms_card, T.aux_numComponents hconn]
  omega

end Pinch
end WaveTurbulence.MoleProp4

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCellProduct
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitRank
import Mathlib.Tactic

/-! # An atom set attached by a single bond

The removed part of a (Y) sequence ending in (Y1), case 2 (DH23 L1929, L1952: "at most one extra bond"), is attached
to the rest by one bond `x` (from `Y` to `c ∉ Y`). Its label is fixed by the charges (boundary identity), the cells of
`N` are those of the piece and those of the rest (a cell meeting both would need two crossing bonds), and
`χ(N) − χ(N∖Y) − χ(N[Y]) = F(N) − F(N∖Y) ≥ 0`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `Y` is attached by exactly one bond, through the dart `x` leaving `Y`. -/
structure OneExit (N : Molecule V D) where
  Y : Finset V
  sub : Y ⊆ N.atoms
  x : D
  cross : crossDarts N Y = {x}

namespace OneExit
variable {N : Molecule V D} (T : OneExit N)

def c : V := N.atom (N.mate T.x)

omit [DecidableEq D] in
theorem x_mem : T.x ∈ crossDarts N T.Y := by rw [T.cross]; exact mem_singleton_self _
omit [DecidableEq D] in
theorem atom_x : N.atom T.x ∈ T.Y := (mem_crossDarts.mp T.x_mem).1
omit [DecidableEq D] in
theorem c_notMem : T.c ∉ T.Y := (mem_crossDarts.mp T.x_mem).2

omit [DecidableEq D] in
theorem eq_of_cross {z : D} (h1 : N.atom z ∈ T.Y) (h2 : N.atom (N.mate z) ∉ T.Y) : z = T.x := by
  have hz : z ∈ crossDarts N T.Y := mem_crossDarts.mpr ⟨h1, h2⟩
  rw [T.cross] at hz; exact mem_singleton.mp hz

omit [DecidableEq D] in
theorem dart_cases (z : D) :
    (N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∨ (N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∨
      z = T.x ∨ z = N.mate T.x := by
  by_cases h1 : N.atom z ∈ T.Y <;> by_cases h2 : N.atom (N.mate z) ∈ T.Y
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inr (Or.inl (T.eq_of_cross h1 h2)))
  · right; right; right
    have := T.eq_of_cross (z := N.mate z) h2 (by rw [N.mate_mate]; exact h1)
    rw [← this, N.mate_mate]
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

theorem card_darts :
    Fintype.card D = Fintype.card (Degen.RetainedDart N (N.atoms \ T.Y)) +
      Fintype.card (Degen.RetainedDart N T.Y) + 2 := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hin : (univ.filter fun z : D => N.atom z ∉ N.atoms \ T.Y ∧ N.atom (N.mate z) ∉ N.atoms \ T.Y) =
      univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y := by
    ext z; simp only [mem_filter, mem_univ, true_and, mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1 (N.atom_mem _), h2 (N.atom_mem _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩
  rw [hin]
  have hex : ({T.x, N.mate T.x} : Finset D).card = 2 := card_pair (fun h => N.mate_ne T.x h.symm)
  have hex_not : ∀ z ∈ ({T.x, N.mate T.x} : Finset D),
      ¬(N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∧ ¬(N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨fun h => T.c_notMem h.2, fun h => h.1 T.atom_x⟩
    · rw [N.mate_mate]; exact ⟨fun h => T.c_notMem h.1, fun h => h.2 T.atom_x⟩
  have hpart : (univ : Finset D) = (univ.filter fun z => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∪ {T.x, N.mate T.x} := by
    ext z
    simp only [mem_univ, mem_union, mem_filter, true_and, mem_insert, mem_singleton, true_iff]
    rcases T.dart_cases z with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hd1 : Disjoint (univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y)
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) := by
    rw [disjoint_filter]; intro z _ h h'; exact h'.1 h.1
  have hd2 : Disjoint ((univ.filter fun z : D => N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∪
      (univ.filter fun z => N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y)) {T.x, N.mate T.x} := by
    rw [disjoint_right]
    intro z hz hzf
    rcases mem_union.mp hzf with h | h
    · exact (hex_not z hz).1 (mem_filter.mp h).2
    · exact (hex_not z hz).2 (mem_filter.mp h).2
  have htot := congrArg Finset.card hpart
  rw [← card_univ, htot, card_union_of_disjoint hd2, card_union_of_disjoint hd1, hex]

theorem bonds_eq : N.bonds.card = (piece N T.Y).bonds.card + (Degen.eraseAtoms N T.Y).bonds.card + 1 := by
  have h1 := Mole.two_mul_card_bonds N
  have h2 := Mole.two_mul_card_bonds (piece N T.Y)
  have h3 := Mole.two_mul_card_bonds (Degen.eraseAtoms N T.Y)
  have h4 := T.card_darts
  omega

omit [DecidableEq D] in
/-- Folding `Y` onto `c` maps paths of `N` to paths of `N ∖ Y`. -/
theorem erase_sameComponent_fold {u v : V} (h : N.SameComponent u v) :
    (Degen.eraseAtoms N T.Y).SameComponent (if u ∈ T.Y then T.c else u) (if v ∈ T.Y then T.c else v) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hcY : N.atom (N.mate T.x) ∉ T.Y := T.c_notMem
    rcases T.dart_cases z with h | h | rfl | rfl
    · simp only [h.1, h.2, ite_true]; exact Relation.EqvGen.refl _
    · simp only [h.1, h.2, ite_false]
      exact Relation.EqvGen.rel _ _ ⟨⟨z, h.1, h.2⟩, rfl, rfl⟩
    · simp only [T.atom_x, hcY, ite_true, ite_false]; exact Relation.EqvGen.refl _
    · simp only [N.mate_mate, T.atom_x, hcY, ite_true, ite_false]; exact Relation.EqvGen.refl _
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

theorem circuitRank_identity :
    N.circuitRank - (Degen.eraseAtoms N T.Y).circuitRank - (piece N T.Y).circuitRank =
      (N.numComponents : ℤ) - (Degen.eraseAtoms N T.Y).numComponents - (piece N T.Y).numComponents + 1 := by
  unfold Molecule.circuitRank
  have hat : N.atoms.card = T.Y.card + (N.atoms \ T.Y).card := by
    rw [card_sdiff_of_subset T.sub]; have := card_le_card T.sub; omega
  rw [T.bonds_eq, hat, piece_atoms T.sub]
  change _ - (((Degen.eraseAtoms N T.Y).bonds.card : ℤ) - ((N.atoms \ T.Y).card : ℤ) + _) - _ = _
  push_cast
  ring

omit [DecidableEq D] in
/-- No cell of `N` meets both `Y` and its complement. -/
theorem cell_sub_or_disjoint {S : Finset V} (hS : MoleProp.IsLadderCell N S) : S ⊆ T.Y ∨ Disjoint S T.Y := by
  classical
  obtain ⟨u, v, hL, rfl⟩ := hS
  have cross : ∀ a b, a ∈ T.Y → b ∉ T.Y → ∀ z, N.atom z = a → N.atom (N.mate z) = b → z = T.x := by
    intro a b ha hb z hza hzb
    exact T.eq_of_cross (hza ▸ ha) (hzb ▸ hb)
  obtain ⟨_, hinj, _, hrung, hrail⟩ := hL
  obtain ⟨su, sv, _⟩ := hrail 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
  -- a double rung cannot cross
  have rung_ok : ∀ j, (u j ∈ T.Y ↔ v j ∈ T.Y) := by
    intro j
    have hne : u j ≠ v j := fun e => by have := hinj (a₁ := .inl j) (a₂ := .inr j) e; simp at this
    have hcard := Degen.card_neighborDarts N hne
    have hcard' := Degen.card_neighborDarts N (Ne.symm hne)
    rw [hrung j] at hcard
    rw [Degen.bondsBetween_comm, hrung j] at hcard'
    constructor
    · intro hu
      by_contra hv
      have hall : ∀ z ∈ Degen.neighborDarts N (u j) (v j), z = T.x := fun z hz =>
        cross _ _ hu hv z ((Degen.mem_neighborDarts N _ _ z).mp hz).1 ((Degen.mem_neighborDarts N _ _ z).mp hz).2
      have := card_le_one.mpr fun a ha b hb => (hall a ha).trans (hall b hb).symm
      omega
    · intro hv
      by_contra hu
      have hall : ∀ z ∈ Degen.neighborDarts N (v j) (u j), z = T.x := fun z hz =>
        cross _ _ hv hu z ((Degen.mem_neighborDarts N _ _ z).mp hz).1 ((Degen.mem_neighborDarts N _ _ z).mp hz).2
      have := card_le_one.mpr fun a ha b hb => (hall a ha).trans (hall b hb).symm
      omega
  have hS4 : ∀ z, z ∈ Molecule.ladderAtoms u v ↔ z = u 0 ∨ z = u 1 ∨ z = v 0 ∨ z = v 1 := by
    intro z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  have r0 := rung_ok 0
  have r1 := rung_ok 1
  by_cases h0 : u 0 ∈ T.Y <;> by_cases h1 : u 1 ∈ T.Y
  · left; intro z hz; rw [hS4] at hz; rcases hz with rfl | rfl | rfl | rfl <;> tauto
  · -- both rails cross from the `0` rung
    exfalso
    have hu01 : u 0 ≠ u 1 := fun e => by have := hinj (a₁ := .inl 0) (a₂ := .inl 1) e; simp at this
    have hv01 : v 0 ≠ v 1 := fun e => by have := hinj (a₁ := .inr 0) (a₂ := .inr 1) e; simp at this
    obtain ⟨zu, hzu⟩ : (Degen.neighborDarts N (u 0) (u 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts N hu01, su]; norm_num
    obtain ⟨zv, hzv⟩ : (Degen.neighborDarts N (v 0) (v 1)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts N hv01, sv]; norm_num
    obtain ⟨hzu1, hzu2⟩ := (Degen.mem_neighborDarts N _ _ _).mp hzu
    obtain ⟨hzv1, hzv2⟩ := (Degen.mem_neighborDarts N _ _ _).mp hzv
    have e1 := cross _ _ h0 h1 zu hzu1 hzu2
    have e2 := cross _ _ (r0.mp h0) (fun h => h1 (r1.mpr h)) zv hzv1 hzv2
    have : u 0 = v 0 := by rw [← hzu1, ← hzv1, e1, e2]
    have := hinj (a₁ := .inl 0) (a₂ := .inr 0) this; simp at this
  · exfalso
    have hu01 : u 0 ≠ u 1 := fun e => by have := hinj (a₁ := .inl 0) (a₂ := .inl 1) e; simp at this
    have hv01 : v 0 ≠ v 1 := fun e => by have := hinj (a₁ := .inr 0) (a₂ := .inr 1) e; simp at this
    obtain ⟨zu, hzu⟩ : (Degen.neighborDarts N (u 1) (u 0)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts N (Ne.symm hu01), Degen.bondsBetween_comm, su]; norm_num
    obtain ⟨zv, hzv⟩ : (Degen.neighborDarts N (v 1) (v 0)).Nonempty := by
      rw [← card_pos, Degen.card_neighborDarts N (Ne.symm hv01), Degen.bondsBetween_comm, sv]; norm_num
    obtain ⟨hzu1, hzu2⟩ := (Degen.mem_neighborDarts N _ _ _).mp hzu
    obtain ⟨hzv1, hzv2⟩ := (Degen.mem_neighborDarts N _ _ _).mp hzv
    have e1 := cross _ _ h1 h0 zu hzu1 hzu2
    have e2 := cross _ _ (r1.mp h1) (fun h => h0 (r0.mpr h)) zv hzv1 hzv2
    have : u 1 = v 1 := by rw [← hzu1, ← hzv1, e1, e2]
    have := hinj (a₁ := .inl 1) (a₂ := .inr 1) this; simp at this
  · right
    refine disjoint_left.mpr fun z hz hzY => ?_
    rw [hS4] at hz; rcases hz with rfl | rfl | rfl | rfl <;> tauto

end OneExit
end WaveTurbulence.MoleProp4

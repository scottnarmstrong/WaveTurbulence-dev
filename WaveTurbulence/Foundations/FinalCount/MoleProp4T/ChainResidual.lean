/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.CompleteY
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2NotRemoved
import Mathlib.Tactic

/-! # The molecule after a complete (Y) sequence

For a chain whose atoms have the degrees of a (Y2) or (Y1) case 2 ending, `𝕄′` (post molecule, resp. `𝕄 ∖ chain`)
has `E′ − 2V′ = E − 2V`; it is connected if `𝕄` is; and, when the chain's triple bond is the only one of `𝕄` and the
sequence is complete, `𝕄′` has no triple bond. These are the facts DH23 L1959 uses to apply Prop 10.2 to `𝕄′`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The bonds of the piece: `2 E(piece) = ∑_{Y} deg − #cross`. -/
theorem two_mul_piece_bonds (N : Molecule V D) {Y : Finset V} (hY : Y ⊆ N.atoms) :
    2 * (piece N Y).bonds.card + (crossDarts N Y).card = ∑ v ∈ Y, N.deg v := by
  classical
  have hsum := Mole.sum_degrees_eq_two_mul_bonds (piece N Y)
  rw [piece_atoms hY] at hsum
  have hsplit : ∀ v ∈ Y, (piece N Y).deg v + ((N.dartsAt v).filter fun z => N.atom (N.mate z) ∉ Y).card =
      N.deg v := by
    intro v hv
    have h := deg_eraseAtoms_add (N := N) (N.atoms \ Y) (fun h => (mem_sdiff.mp h).2 hv)
    have heq : Degen.removedDartsAt N (N.atoms \ Y) v = (N.dartsAt v).filter fun z => N.atom (N.mate z) ∉ Y := by
      unfold Degen.removedDartsAt
      congr 1; ext z
      simp only [mem_sdiff, N.atom_mem, true_and]
    rw [heq] at h
    exact h
  have hcross : ∑ v ∈ Y, ((N.dartsAt v).filter fun z => N.atom (N.mate z) ∉ Y).card = (crossDarts N Y).card := by
    rw [card_eq_sum_card_fiberwise (s := crossDarts N Y) (t := Y) (f := N.atom)
      (fun z hz => (mem_crossDarts.mp hz).1)]
    refine sum_congr rfl fun v _ => ?_
    congr 1; ext z
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and, mem_crossDarts]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ ‹v ∈ Y›, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  rw [← sum_congr rfl hsplit, sum_add_distrib, hcross, ← hsum]

omit [DecidableEq D] in
/-- After erasing a set, an atom of it has no bonds. -/
theorem bondsBetween_erase_of_mem (N : Molecule V D) (Y : Finset V) {p q : V} (hp : p ∈ Y) :
    (Degen.eraseAtoms N Y).bondsBetween p q = 0 := by
  classical
  unfold Molecule.bondsBetween Molecule.bonds
  rw [card_eq_zero, filter_filter]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨_, _, h⟩ := mem_filter.mp hz
  change s(N.atom z.val, N.atom (N.mate z.val)) = s(p, q) at h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact z.property.1 (h1 ▸ hp)
  · exact z.property.2 (h2 ▸ hp)

omit [DecidableEq D] in
/-- With degrees at most four and `E = 2V − 1`, some atom has degree `≠ 4`. -/
theorem exists_deg_ne_four (N : Molecule V D) (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hE : (N.bonds.card : ℤ) = 2 * N.atoms.card - 1) : ∃ z ∈ N.atoms, N.deg z ≠ 4 ∧ N.deg z ≤ 3 := by
  classical
  by_contra h
  push Not at h
  have hall : ∀ v ∈ N.atoms, N.deg v = 4 := by
    intro v hv
    have h1 := hcap v hv
    have h2 := Mole.outdeg_add_indeg N v
    by_contra hne
    exact absurd (h v hv hne) (by omega)
  have hs := Mole.sum_degrees_eq_two_mul_bonds N
  rw [sum_congr rfl hall, sum_const, smul_eq_mul] at hs
  omega

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **Bond count of the post molecule** when every atom of `Y` has degree four. -/
theorem post_bonds_card (hdegY : ∀ v ∈ T.Y, N.deg v = 4) :
    (T.post.bonds.card : ℤ) = N.bonds.card - 2 * T.Y.card := by
  have h1 := two_mul_piece_bonds N T.sub
  rw [T.cross, card_pair T.ne, sum_congr rfl hdegY, sum_const, smul_eq_mul] at h1
  have h2 := T.bonds_eq
  have h3 := T.post_bonds_eq
  omega

theorem post_atoms_card : (T.post.atoms.card : ℤ) = N.atoms.card - T.Y.card := by
  rw [T.post_atoms, card_sdiff_of_subset T.sub]
  have := card_le_card T.sub
  omega

end TwoExit

namespace OneExit
variable {N : Molecule V D} (T : OneExit N)

/-- **Bond count of `N ∖ Y`** when the degrees on `Y` add up to `4|Y| − 1`. -/
theorem erase_bonds_card (hdegY : ∑ v ∈ T.Y, N.deg v = 4 * T.Y.card - 1) (hY : 1 ≤ T.Y.card) :
    ((Degen.eraseAtoms N T.Y).bonds.card : ℤ) = N.bonds.card - 2 * T.Y.card := by
  have h1 := two_mul_piece_bonds N T.sub
  rw [T.cross, card_singleton, hdegY] at h1
  have h2 := T.bonds_eq
  omega

omit [DecidableEq D] in
theorem erase_connected (hconn : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v) :
    ∀ u ∈ (Degen.eraseAtoms N T.Y).atoms, ∀ v ∈ (Degen.eraseAtoms N T.Y).atoms,
      (Degen.eraseAtoms N T.Y).SameComponent u v := by
  intro u hu v hv
  have hu' := mem_sdiff.mp hu
  have hv' := mem_sdiff.mp hv
  have h := T.erase_sameComponent_fold (hconn u hu'.1 v hv'.1)
  rw [ite_of_not hu'.2, ite_of_not hv'.2] at h
  exact h

end OneExit

namespace YChain
variable {M : Molecule V D} (C : YChain M)

omit [DecidableEq D] in
/-- The chain atoms: `2 (n + 1)` of them. -/
theorem card_set : C.set.card = 2 * (C.n + 1) := by
  classical
  have h1 : ((range (C.n + 1)).image C.a).card = C.n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact C.inj_a i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h
  have h2 : ((range (C.n + 1)).image C.b).card = C.n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact C.inj_b i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h
  have hdisj : Disjoint ((range (C.n + 1)).image C.a) ((range (C.n + 1)).image C.b) := by
    rw [disjoint_left]
    intro v hv hv'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    obtain ⟨j, hj, h⟩ := mem_image.mp hv'
    exact C.ne_ab i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h.symm
  unfold set
  rw [card_union_of_disjoint hdisj, h1, h2]
  ring

omit [DecidableEq D] in
/-- Degrees on the chain of a (Y1) case 2 ending add up to `4|Y| − 1`. -/
theorem sum_deg_Y1End2 (E : Y1End2 C) : ∑ v ∈ C.set, M.deg v = 4 * C.set.card - 1 := by
  classical
  have hlast : M.deg (C.a C.n) + M.deg (C.b C.n) = 7 := E.hdeg
  have hrest : ∀ v ∈ C.set, v ≠ C.a C.n → v ≠ C.b C.n → M.deg v = 4 := by
    intro v hv h1 h2
    obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
    · rcases Nat.lt_or_ge i C.n with h | h
      · exact (C.sat i h).1
      · exact absurd (by rw [le_antisymm hi h]) h1
    · rcases Nat.lt_or_ge i C.n with h | h
      · exact (C.sat i h).2
      · exact absurd (by rw [le_antisymm hi h]) h2
  have ha := C.a_mem le_rfl
  have hb := C.b_mem le_rfl
  have hab : C.a C.n ≠ C.b C.n := C.ne_ab _ le_rfl _ le_rfl
  rw [← add_sum_erase _ _ ha, ← add_sum_erase _ _ (mem_erase.mpr ⟨hab.symm, hb⟩)]
  have hrest' : ∀ v ∈ (C.set.erase (C.a C.n)).erase (C.b C.n), M.deg v = 4 := fun v hv => by
    obtain ⟨h1, h2⟩ := mem_erase.mp hv
    obtain ⟨h3, h4⟩ := mem_erase.mp h2
    exact hrest v h4 h3 h1
  rw [sum_congr rfl hrest', sum_const, smul_eq_mul, card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩),
    card_erase_of_mem ha]
  have := C.card_set
  have h2 : 2 ≤ C.set.card := by omega
  have h3 : #C.set - 1 - 1 + 2 = #C.set := by omega
  rw [← h3] at ⊢
  omega

end YChain

end WaveTurbulence.MoleProp4

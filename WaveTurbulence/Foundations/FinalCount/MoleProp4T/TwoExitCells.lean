/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitPost
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.CellGap
public import WaveTurbulence.Foundations.FinalCount.MoleProp4.BondInsertion
import Mathlib.Tactic

/-! # Cells around a two-exit removal

The new bond `d → c` changes only the cells containing `c`; a cell of `N` meeting both `Y` and its complement contains
an exit atom (its crossing bonds are exits). So, apart from at most six cells (`≤ 2` through each of `c`, the atom of
`x`, the atom of `y`), the cells of `N` are those of the piece and those of the post molecule avoiding `c`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
theorem directed_addBond_iff (M : Molecule V D) (a b x y : V) :
    (Mole.addBond M a b).Directed x y ↔ M.Directed x y ∨ (x = a ∧ y = b) := by
  constructor
  · rintro ⟨z, hz, hx, hy⟩
    rcases z with z | t
    · exact Or.inl ⟨z, hz, hx, hy⟩
    · change t = true at hz
      subst hz
      exact Or.inr ⟨hx.symm, hy.symm⟩
  · rintro (⟨z, hz, hx, hy⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Sum.inl z, hz, hx, hy⟩
    · exact ⟨Sum.inr true, rfl, rfl, rfl⟩

omit [DecidableEq D] in
/-- A ladder avoiding the second end `b` of the added bond is unaffected (`a, b` already atoms). -/
theorem sourceLadder_addBond_iff (M : Molecule V D) {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    {u v : Fin 2 → V} (hbS : b ∉ Molecule.ladderAtoms u v) :
    Degen.SourceLadder (Mole.addBond M a b) u v ↔ Degen.SourceLadder M u v := by
  have hmem : ∀ j, u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := fun j =>
    ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ j)), mem_union_right _ (mem_image_of_mem _ (mem_univ j))⟩
  have hne : ∀ x y, x ∈ Molecule.ladderAtoms u v → s(a, b) ≠ s(x, y) ∨ y ∈ Molecule.ladderAtoms u v →
      True := fun _ _ _ _ => trivial
  have hbb : ∀ x y, x ∈ Molecule.ladderAtoms u v → y ∈ Molecule.ladderAtoms u v →
      (Mole.addBond M a b).bondsBetween x y = M.bondsBetween x y := by
    intro x y hx hy
    rw [addBond_bondsBetween]
    have : ¬ s(a, b) = s(x, y) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hbS (h2 ▸ hy)
      · exact hbS (h2 ▸ hx)
    simp only [this, ite_false, add_zero]
  have hdir : ∀ x y, y ∈ Molecule.ladderAtoms u v → x ∈ Molecule.ladderAtoms u v →
      ((Mole.addBond M a b).Directed x y ↔ M.Directed x y) := by
    intro x y hy hx
    rw [directed_addBond_iff]
    constructor
    · rintro (h | ⟨_, rfl⟩)
      · exact h
      · exact absurd hy hbS
    · exact Or.inl
  have hat : ∀ z, z ∈ (Mole.addBond M a b).atoms ↔ z ∈ M.atoms := by
    intro z
    change z ∈ insert a (insert b M.atoms) ↔ _
    rw [insert_eq_of_mem hb, insert_eq_of_mem ha]
  unfold Degen.SourceLadder
  simp only [hat]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · exact forall_congr' fun j => by rw [hbb _ _ (hmem j).1 (hmem j).2]
  · refine forall_congr' fun j => ?_
    have h0 := hmem j.castSucc
    have h1 := hmem j.succ
    rw [hbb _ _ h0.1 h1.1, hbb _ _ h0.2 h1.2, hdir _ _ h1.1 h0.1, hdir _ _ h0.2 h1.2]

omit [DecidableEq D] in
/-- Degrees after adding a bond `a → b`. -/
theorem deg_addBond (M : Molecule V D) (a b z : V) :
    (Mole.addBond M a b).deg z = M.deg z + (if a = z then 1 else 0) + (if b = z then 1 else 0) := by
  have h := sum_dartsAt_addBond M a b z (fun _ => (1 : ℕ))
  simp only [← card_eq_sum_ones] at h
  exact h

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- Cells of the post molecule avoiding `c` are the cells of `N` avoiding `Y` and `c`. -/
theorem isLadderCell_post_iff {S : Finset V} (hcS : T.c ∉ S) :
    MoleProp.IsLadderCell T.post S ↔ MoleProp.IsLadderCell N S ∧ Disjoint S T.Y := by
  rw [← MoleProp.isLadderCell_erase_iff]
  constructor
  · rintro ⟨u, v, h, rfl⟩
    exact ⟨u, v, (sourceLadder_addBond_iff _ T.d_mem T.c_mem hcS).mp h, rfl⟩
  · rintro ⟨u, v, h, rfl⟩
    exact ⟨u, v, (sourceLadder_addBond_iff _ T.d_mem T.c_mem hcS).mpr h, rfl⟩

/-- The post molecule has the degrees of `N` on the surviving atoms. -/
theorem post_deg {v : V} (hv : v ∉ T.Y) : T.post.deg v = N.deg v := by
  have h1 := deg_addBond (Degen.eraseAtoms N T.Y) T.d T.c v
  have h2 := deg_eraseAtoms_add (N := N) T.Y hv
  have h3 := congrArg Finset.card (T.removedDartsAt_eq hv)
  change T.post.deg v = _ at h1
  have hcd := T.c_ne_d
  have hmm := T.mate_x_ne_mate_y
  by_cases hc : v = T.c
  · subst hc
    simp only [ite_true, Ne.symm hcd, hcd, ite_false, union_empty, card_singleton] at h1 h3
    omega
  · by_cases hd : v = T.d
    · subst hd
      simp only [hc, hcd, ite_true, ite_false, empty_union, card_singleton] at h1 h3
      omega
    · simp only [hc, hd, Ne.symm hc, Ne.symm hd, ite_false, union_empty, card_empty, add_zero] at h1 h3
      omega

theorem post_loop_free (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    ∀ z, T.post.atom z ≠ T.post.atom (T.post.mate z) := by
  rintro (z | t)
  · exact hloop z.val
  · cases t
    · exact T.c_ne_d
    · exact Ne.symm T.c_ne_d

/-- A cell of `N` meeting `Y` and its complement contains the atom of an exit. -/
theorem straddle_mem_exit {S : Finset V} (hS : MoleProp.IsLadderCell N S) (hin : ∃ a ∈ S, a ∈ T.Y)
    (hout : ∃ a ∈ S, a ∉ T.Y) : N.atom T.x ∈ S ∨ N.atom T.y ∈ S := by
  obtain ⟨u, v, hL, rfl⟩ := hS
  -- a bond between an atom of `Y` and one outside starts at an exit atom
  have cross : ∀ a b, a ∈ T.Y → b ∉ T.Y → 0 < N.bondsBetween a b → a = N.atom T.x ∨ a = N.atom T.y := by
    intro a b ha hb hpos
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    rw [← Degen.card_neighborDarts N hab] at hpos
    obtain ⟨z, hz⟩ := card_pos.mp hpos
    obtain ⟨hza, hzb⟩ := (Degen.mem_neighborDarts N a b z).mp hz
    rcases T.eq_of_cross (z := z) (hza ▸ ha) (hzb ▸ hb) with rfl | rfl
    · exact Or.inl hza.symm
    · exact Or.inr hza.symm
  have hmem : ∀ j, u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := fun j =>
    ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ j)), mem_union_right _ (mem_image_of_mem _ (mem_univ j))⟩
  have pick : ∀ a b, a ∈ Molecule.ladderAtoms u v → a ∈ T.Y → b ∉ T.Y → 0 < N.bondsBetween a b →
      N.atom T.x ∈ Molecule.ladderAtoms u v ∨ N.atom T.y ∈ Molecule.ladderAtoms u v := by
    intro a b haS ha hb hp
    rcases cross a b ha hb hp with rfl | rfl
    · exact Or.inl haS
    · exact Or.inr haS
  obtain ⟨_, _, _, hrung, hrail⟩ := hL
  obtain ⟨su, sv, _⟩ := hrail 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
  have bc := fun a b => Degen.bondsBetween_comm N a b
  have hS4 : ∀ z, z ∈ Molecule.ladderAtoms u v ↔ z = u 0 ∨ z = u 1 ∨ z = v 0 ∨ z = v 1 := by
    intro z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  -- check every bond of the cell
  have hpos2 : ∀ j, 0 < N.bondsBetween (u j) (v j) := fun j => by rw [hrung j]; norm_num
  by_contra hno
  push Not at hno
  have nocross : ∀ a b, a ∈ Molecule.ladderAtoms u v → b ∈ Molecule.ladderAtoms u v → 0 < N.bondsBetween a b →
      (a ∈ T.Y ↔ b ∈ T.Y) := by
    intro a b ha hb hp
    by_contra hiff
    by_cases haY : a ∈ T.Y
    · have hbY : b ∉ T.Y := fun h => hiff ⟨fun _ => h, fun _ => haY⟩
      rcases pick a b ha haY hbY hp with h | h
      exacts [hno.1 h, hno.2 h]
    · have hbY : b ∈ T.Y := by by_contra h; exact hiff ⟨fun h' => absurd h' haY, fun h' => absurd h' h⟩
      rcases pick b a hb hbY haY (by rw [bc]; exact hp) with h | h
      exacts [hno.1 h, hno.2 h]
  have e00 := nocross _ _ (hmem 0).1 (hmem 0).2 (hpos2 0)
  have e11 := nocross _ _ (hmem 1).1 (hmem 1).2 (hpos2 1)
  have eu := nocross _ _ (hmem 0).1 (hmem 1).1 (by rw [su]; norm_num)
  obtain ⟨a, haS, haY⟩ := hin
  obtain ⟨b, hbS, hbY⟩ := hout
  rw [hS4] at haS hbS
  rcases haS with rfl | rfl | rfl | rfl <;> rcases hbS with rfl | rfl | rfl | rfl <;> tauto

end TwoExit
end WaveTurbulence.MoleProp4

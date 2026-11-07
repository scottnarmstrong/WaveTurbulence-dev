/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseIV
import Mathlib.Tactic

/-! # Cells of a merged molecule are good (finalcount-g8)

`MergeAt` carries the hypothesis that every cell of the merged molecule is `GoodCell`. This module discharges it for
`case_merge`: (1) the merge of `M ∖ ℓ` has an atom of degree three (an end of `ℓ`) and is connected; (2) the merge of `M`
is 4-regular and connected, so it has at least five atoms once `|M| ≥ 6`; `six_le_card` shows `|M| ≥ 6` when a double bond
`v₁ = v₂` lies away from the ends of `ℓ`, which have no double bond.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **At least six atoms.** -/
theorem six_le_card {M : Molecule V D} (hM : IsCore M) {p q v₁ v₂ : V} (hp : p ∈ M.atoms) (hq : q ∈ M.atoms)
    (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms) (hpq : p ≠ q) (hv : v₁ ≠ v₂) (hpv₁ : p ≠ v₁) (hpv₂ : p ≠ v₂)
    (hqv₁ : q ≠ v₁) (hqv₂ : q ≠ v₂) (hbb : M.bondsBetween v₁ v₂ = 2)
    (hp1 : ∀ w, M.bondsBetween p w ≠ 2) (hq1 : ∀ w, M.bondsBetween q w ≠ 2) : 6 ≤ M.atoms.card := by
  classical
  have hdeg := fun u (hu : u ∈ M.atoms) => (hM.reg u hu).symm.trans (deg_eq_sum_bb M hM.loop u)
  have hsub : ({p, q, v₁, v₂} : Finset V) ⊆ M.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hc4 : ({p, q, v₁, v₂} : Finset V).card = 4 := by
    rw [card_insert_of_notMem (by simp [hpq, hpv₁, hpv₂]), card_insert_of_notMem (by simp [hqv₁, hqv₂]), card_pair hv]
  -- `p` has at least four neighbours
  have h5 : 5 ≤ M.atoms.card := by
    have h := hdeg p hp
    have hle : ∑ w ∈ M.atoms.erase p, M.bondsBetween p w ≤ ∑ _w ∈ M.atoms.erase p, 1 :=
      sum_le_sum fun w _ => by have := hM.le2 p w; have := hp1 w; omega
    rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem hp] at hle
    have := card_pos.mpr ⟨p, hp⟩
    omega
  by_contra hlt
  have hc5 : M.atoms.card = 5 := by omega
  obtain ⟨w, hw, hwn⟩ := exists_mem_notMem_of_card_lt_card (by omega : ({p, q, v₁, v₂} : Finset V).card < M.atoms.card)
  have hwp : w ≠ p := fun h => hwn (by simp [h])
  have hwq : w ≠ q := fun h => hwn (by simp [h])
  have hw1 : w ≠ v₁ := fun h => hwn (by simp [h])
  have hw2 : w ≠ v₂ := fun h => hwn (by simp [h])
  have hatoms : M.atoms = {p, q, v₁, v₂, w} := by
    symm
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by
      rw [hc5, card_insert_of_notMem (by simp [hpq, hpv₁, hpv₂, hwp.symm]),
        card_insert_of_notMem (by simp [hqv₁, hqv₂, hwq.symm]), card_insert_of_notMem (by simp [hv, hw1.symm]),
        card_pair hw2.symm])
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hself : ∀ u, M.bondsBetween u u = 0 := fun u => bondsBetween_self_eq_zero hM.loop u
  have hrow : ∀ u ∈ M.atoms, 4 = M.bondsBetween u p + M.bondsBetween u q + M.bondsBetween u v₁ +
      M.bondsBetween u v₂ + M.bondsBetween u w := by
    intro u hu
    have h1 := hdeg u hu
    have h2 := Finset.add_sum_erase M.atoms (fun x => M.bondsBetween u x) hu
    rw [hself u, zero_add, ← h1] at h2
    rw [hatoms] at h2
    rw [sum_insert (by simp [hpq, hpv₁, hpv₂, hwp.symm]), sum_insert (by simp [hqv₁, hqv₂, hwq.symm]),
      sum_insert (by simp [hv, hw1.symm]), sum_pair hw2.symm] at h2
    have := hM.reg u hu; omega
  have hw' : w ∈ M.atoms := hw
  have rp := hrow p hp
  have rq := hrow q hq
  have r1 := hrow v₁ hv₁
  have r2 := hrow v₂ hv₂
  have rw' := hrow w hw'
  have s1 := bondsBetween_symm M p q
  have s2 := bondsBetween_symm M p v₁
  have s3 := bondsBetween_symm M p v₂
  have s4 := bondsBetween_symm M p w
  have s5 := bondsBetween_symm M q v₁
  have s6 := bondsBetween_symm M q v₂
  have s7 := bondsBetween_symm M q w
  have s8 := bondsBetween_symm M v₁ v₂
  have s9 := bondsBetween_symm M v₁ w
  have s10 := bondsBetween_symm M v₂ w
  have t1 := hM.le2 p q; have t2 := hM.le2 p v₁; have t3 := hM.le2 p v₂; have t4 := hM.le2 p w
  have t5 := hM.le2 q v₁; have t6 := hM.le2 q v₂; have t7 := hM.le2 q w
  have u1 := hp1 q; have u2 := hp1 v₁; have u3 := hp1 v₂; have u4 := hp1 w
  have u5 := hq1 v₁; have u6 := hq1 v₂; have u7 := hq1 w; have u8 := hq1 p
  rw [hself p] at rp; rw [hself q] at rq; rw [hself v₁] at r1; rw [hself v₂] at r2; rw [hself w] at rw'
  omega

omit [DecidableEq D] in
/-- Every cell of the merge of a core molecule with at least six atoms is good. -/
theorem goodCell_merge_core {M : Molecule V D} (hM : IsCore M) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms)
    (hne : v₁ ≠ v₂) (h6 : 6 ≤ M.atoms.card) :
    ∀ S' ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), GoodCell (mergePair M v₁ v₂ hv₁ hne) S' := by
  intro S' hS'
  have hc := Merge.card_atoms (M := M) (hv₁ := hv₁) (hne := hne) hv₂
  exact goodCell_of_connected (Merge.connected hM.conn) (by omega) hS'

/-- Every cell of the merge of `M ∖ ℓ` is good (an end of `ℓ` has degree three). -/
theorem goodCell_merge_erase {M : Molecule V D} (hM : IsCore M) (e : D) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms)
    (hne : v₁ ≠ v₂) (hp1 : M.atom e ≠ v₁) (hp2 : M.atom e ≠ v₂) :
    ∀ S' ∈ MoleProp.ladderCells (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne),
      GoodCell (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne) S' := by
  intro S' hS'
  have hz : M.atom e ∈ (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne).atoms := by
    exact mem_erase.mpr ⟨hp2, M.atom_mem e⟩
  have hd := Merge.deg_of_ne (M := MoleProp.eraseBond M e) (hv₁ := hv₁) (hne := hne) hp1 hp2
  exact goodCell_of_connected_low (Merge.connected (hM.eraseBond_conn e)) hz (by rw [hd, hM.eraseBond_deg_p e]) hS'

end WaveTurbulence.MoleProp4

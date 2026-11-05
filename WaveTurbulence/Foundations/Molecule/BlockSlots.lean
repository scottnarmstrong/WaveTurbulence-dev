/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockParent
import Mathlib.Tactic

/-! # The four possible incidence patterns at a block joint
DH23 Proposition 4.12 and TARGET `block_clcn`: the two internal slots
have opposite parity, as required by one incoming and one outgoing bond.
-/

public section
namespace WaveTurbulence.Mole
open Finset TTree
variable {w : ℕ} (G : Garden w)

/-- Actual occupied internal incidence positions. -/
@[expose] noncomputable def internalPositions (S : Finset (GBranch G.tree))
    (v : GBranch G.tree) : Finset (Fin 4) :=
  ((G.molecule.dartsAt v).filter (G.molecule.InGroup S)).image (dartPosition G)

theorem mem_internalPositions {S : Finset (GBranch G.tree)} {v : GBranch G.tree} {i : Fin 4} :
    i ∈ internalPositions G S v ↔ ∃ x : GardenDart G,
      G.molecule.atom x = v ∧ G.molecule.InGroup S x ∧ dartPosition G x = i := by
  simp only [internalPositions,mem_image,mem_filter,mem_dartsAt]
  aesop

theorem card_internalPositions (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    (internalPositions G S v).card = G.molecule.degIn S v := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  apply atom_position_injective G
  exact Prod.ext (((mem_dartsAt _ _ _).mp (mem_filter.mp hx).1).trans
    ((mem_dartsAt _ _ _).mp (mem_filter.mp hy).1).symm) he

theorem zero_mem_internalPositions {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) : 0 ∈ internalPositions G S v ↔ InternalParent G S v := by
  constructor
  · intro hz
    obtain ⟨x,hx,hg,hp⟩ := (mem_internalPositions G).mp hz
    obtain ⟨c,rfl⟩ := (position_zero_iff G x).mp hp
    change c.1 = v at hx
    subst v
    exact ⟨c.2,hg.2⟩
  · rintro ⟨hn,hp⟩
    exact (mem_internalPositions G).mpr ⟨.inl (⟨v,hn⟩,false),rfl,⟨hv,hp⟩,rfl⟩

theorem joint_positions_shape {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (ho : G.molecule.outIn S v = 1) (hi : G.molecule.inIn S v = 1) :
    internalPositions G S v = {0,1} ∨ internalPositions G S v = {0,3} ∨
    internalPositions G S v = {1,2} ∨ internalPositions G S v = {2,3} := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 <
      ((G.molecule.dartsAt v).filter (fun x => G.molecule.InGroup S x ∧ G.molecule.out x = true)).card by
    change 0 < G.molecule.outIn S v
    omega)
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 <
      ((G.molecule.dartsAt v).filter (fun x => G.molecule.InGroup S x ∧ G.molecule.out x = false)).card by
    change 0 < G.molecule.inIn S v
    omega)
  obtain ⟨hxv,hxg,hxo⟩ := mem_filter.mp hx
  obtain ⟨hyv,hyg,hyo⟩ := mem_filter.mp hy
  have hxv := (mem_dartsAt _ _ _).mp hxv
  have hyv := (mem_dartsAt _ _ _).mp hyv
  have hp := dart_out_profile G x
  have hq := dart_out_profile G y
  rw [hxv,hxo] at hp
  rw [hyv,hyo] at hq
  have hxy : dartPosition G x ≠ dartPosition G y := by
    intro he
    rw [he] at hp
    exact Bool.noConfusion (hp.trans hq.symm)
  have he : internalPositions G S v = {dartPosition G x,dartPosition G y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i him
      simp only [mem_insert,mem_singleton] at him
      rcases him with rfl | rfl
      · exact (mem_internalPositions G).mpr ⟨x,hxv,hxg,rfl⟩
      · exact (mem_internalPositions G).mpr ⟨y,hyv,hyg,rfl⟩
    · rw [card_internalPositions]
      have hd := outIn_add_inIn G.molecule S v
      rw [ho,hi] at hd
      simp only [card_pair hxy]
      omega
  have hf : ∀ (s : Bool) (i j : Fin 4),
      (if s then decide (i.val%2 = 0) else decide (i.val%2 = 1)) = true →
      (if s then decide (j.val%2 = 0) else decide (j.val%2 = 1)) = false →
      ({i,j} : Finset (Fin 4)) = {0,1} ∨ ({i,j} : Finset (Fin 4)) = {0,3} ∨
      ({i,j} : Finset (Fin 4)) = {1,2} ∨ ({i,j} : Finset (Fin 4)) = {2,3} := by decide
  rw [he]
  by_cases hs : G.sign v.toNode = 1
  · exact hf true _ _ (by simpa only [hs,ite_true,Bool.true_eq] using hp.symm)
      (by simpa only [hs,ite_true,Bool.true_eq] using hq.symm)
  · exact hf false _ _ (by simpa only [hs,ite_false,Bool.false_eq_true,ite_false] using hp.symm)
      (by simpa only [hs,ite_false,Bool.false_eq_true,ite_false] using hq.symm)

end WaveTurbulence.Mole

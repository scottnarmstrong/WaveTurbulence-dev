/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Common
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCells
import Mathlib.Tactic

/-! # The post molecule of a two-exit removal: caps, the new bond, and erasing around it

* `post` keeps the in/out caps: the new bond `d → c` replaces the removed exits `x` (into `c`) and `y` (out of `d`).
* For a (Y2) ending, `{c, d}` are the far ends of the two exits.
* Erasing a set `Z ∋ c, d` from `post` deletes the new bond, and `post ∖ Z ≅ N ∖ (Y ∪ Z)`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [DecidableEq D] in
theorem card_filter_sum' (p : D ⊕ Bool → Prop) [DecidablePred p] :
    (univ.filter p).card = (univ.filter (fun x : D => p (.inl x))).card +
      (univ.filter (fun x : Bool => p (.inr x))).card := by
  have h : univ.filter p = (univ.filter (fun x : D => p (.inl x))).disjSum
      (univ.filter (fun x : Bool => p (.inr x))) := by
    ext x
    cases x <;> simp
  rw [h, card_disjSum]

omit [DecidableEq D] in
/-- The new incoming incidence occurs exactly at the second endpoint. -/
theorem addBond_indeg' (M : Molecule V D) (a b z : V) :
    (Mole.addBond M a b).indeg z = M.indeg z + (if b = z then 1 else 0) := by
  classical
  change ((univ.filter (fun x : D ⊕ Bool => (Mole.addBond M a b).atom x = z)).filter
    (fun x => (Mole.addBond M a b).out x = false)).card = _
  rw [filter_filter, card_filter_sum']
  change (univ.filter (fun x : D => M.atom x = z ∧ M.out x = false)).card +
    (univ.filter (fun x : Bool => (if x then a else b) = z ∧ x = false)).card = _
  rw [show (univ : Finset Bool) = {true, false} by decide]
  have hleft : (univ.filter (fun x : D => M.atom x = z ∧ M.out x = false)).card = M.indeg z := by
    simp only [Molecule.indeg, Molecule.dartsAt, filter_filter]
  rw [hleft]
  by_cases hb : b = z <;> simp [filter_insert, filter_singleton, hb]

/-- Erasing a set loses a removed dart from the directional count. -/
theorem card_dir_erase_lt (N : Molecule V D) (Y : Finset V) {v : V} (_hv : v ∉ Y) (bo : Bool) {z : D}
    (hz : N.atom z = v) (hzY : N.atom (N.mate z) ∈ Y) (hzo : N.out z = bo) :
    (((Degen.eraseAtoms N Y).dartsAt v).filter fun x => (Degen.eraseAtoms N Y).out x = bo).card + 1 ≤
      ((N.dartsAt v).filter fun x => N.out x = bo).card := by
  classical
  have himg : (((Degen.eraseAtoms N Y).dartsAt v).filter fun x => (Degen.eraseAtoms N Y).out x = bo).image
      (fun x => x.val) ⊆ ((N.dartsAt v).filter fun x => N.out x = bo).erase z := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx
    refine mem_erase.mpr ⟨fun h => x.property.2 (h ▸ hzY), ?_⟩
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and]
    exact hx
  have hzmem : z ∈ (N.dartsAt v).filter fun x => N.out x = bo := by
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and]; exact ⟨hz, hzo⟩
  have h1 := card_le_card himg
  rw [card_image_of_injective _ Subtype.val_injective, card_erase_of_mem hzmem] at h1
  have := card_pos.mpr ⟨z, hzmem⟩
  omega

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The post molecule keeps the in/out caps.** -/
theorem post_caps (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) :
    ∀ v ∈ T.post.atoms, T.post.outdeg v ≤ 2 ∧ T.post.indeg v ≤ 2 := by
  intro v hv
  rw [T.post_atoms] at hv
  obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
  have hc := hcap v hvN
  have hle : ∀ bo : Bool, (((Degen.eraseAtoms N T.Y).dartsAt v).filter
      fun x => (Degen.eraseAtoms N T.Y).out x = bo).card ≤ ((N.dartsAt v).filter fun x => N.out x = bo).card := by
    intro bo
    refine card_le_card_of_injOn (fun x => x.val) ?_ (fun x _ y _ h => Subtype.ext h)
    intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx
  constructor
  · unfold post
    rw [addBond_outdeg]
    by_cases hd : T.d = v
    · rw [ite_of_pos hd]
      have hy := T.y_mem
      have := card_dir_erase_lt N T.Y hvY true (z := N.mate T.y) (by rw [← hd]; rfl)
        (by rw [N.mate_mate]; exact T.atom_y) (by rw [N.out_mate, T.out_y]; rfl)
      unfold Molecule.outdeg at hc ⊢
      omega
    · rw [ite_of_not hd, add_zero]
      exact (hle true).trans hc.1
  · unfold post
    rw [addBond_indeg']
    by_cases hcv : T.c = v
    · rw [ite_of_pos hcv]
      have := card_dir_erase_lt N T.Y hvY false (z := N.mate T.x) (by rw [← hcv]; rfl)
        (by rw [N.mate_mate]; exact T.atom_x) (by rw [N.out_mate, T.out_x]; rfl)
      unfold Molecule.indeg at hc ⊢
      omega
    · rw [ite_of_not hcv, add_zero]
      exact (hle false).trans hc.2

/-- **Connectivity passes to the post molecule.** -/
theorem post_connected (hconn : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v) :
    ∀ u ∈ T.post.atoms, ∀ v ∈ T.post.atoms, T.post.SameComponent u v := by
  intro u hu v hv
  rw [T.post_atoms] at hu hv
  have h := T.post_sameComponent_fold (hconn u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1)
  rw [ite_of_not (mem_sdiff.mp hu).2, ite_of_not (mem_sdiff.mp hv).2] at h
  exact h

/-- Erasing `Z ∋ c, d` from the post molecule is erasing `Y ∪ Z` from `N`. -/
def postEraseEquiv (Z : Finset V) (hc : T.c ∈ Z) (hd : T.d ∈ Z) :
    Degen.RetainedDart T.post Z ≃ Degen.RetainedDart N (T.Y ∪ Z) where
  toFun z := match z with
    | ⟨Sum.inl w, h⟩ => ⟨w.val, fun h' => (mem_union.mp h').elim w.property.1 h.1,
        fun h' => (mem_union.mp h').elim w.property.2 h.2⟩
    | ⟨Sum.inr bo, h⟩ => absurd (by cases bo <;> [exact hc; exact hd]) h.1
  invFun y := ⟨Sum.inl ⟨y.val, fun h => y.property.1 (mem_union_left _ h),
      fun h => y.property.2 (mem_union_left _ h)⟩,
    fun h => y.property.1 (mem_union_right _ h), fun h => y.property.2 (mem_union_right _ h)⟩
  left_inv z := by
    obtain ⟨z | bo, h⟩ := z
    · rfl
    · exact absurd (by cases bo <;> [exact hc; exact hd]) h.1
  right_inv y := rfl

theorem postEraseEquiv_facts (Z : Finset V) (hc : T.c ∈ Z) (hd : T.d ∈ Z) :
    (Degen.eraseAtoms T.post Z).atoms = (Degen.eraseAtoms N (T.Y ∪ Z)).atoms ∧
    (∀ x, (Degen.eraseAtoms N (T.Y ∪ Z)).atom (T.postEraseEquiv Z hc hd x) = (Degen.eraseAtoms T.post Z).atom x) ∧
    (∀ x, (Degen.eraseAtoms N (T.Y ∪ Z)).mate (T.postEraseEquiv Z hc hd x) =
      T.postEraseEquiv Z hc hd ((Degen.eraseAtoms T.post Z).mate x)) ∧
    (∀ x, (Degen.eraseAtoms N (T.Y ∪ Z)).out (T.postEraseEquiv Z hc hd x) = (Degen.eraseAtoms T.post Z).out x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change T.post.atoms \ Z = N.atoms \ (T.Y ∪ Z)
    rw [T.post_atoms, sdiff_sdiff_left]; rfl
  · rintro ⟨z | bo, h⟩
    · rfl
    · exact absurd (by cases bo <;> [exact hc; exact hd]) h.1
  · rintro ⟨z | bo, h⟩
    · rfl
    · exact absurd (by cases bo <;> [exact hc; exact hd]) h.1
  · rintro ⟨z | bo, h⟩
    · rfl
    · exact absurd (by cases bo <;> [exact hc; exact hd]) h.1

theorem afree_post_erase_le (Z : Finset V) (hc : T.c ∈ Z) (hd : T.d ∈ Z) {d : ℕ} (L γ δ η C1 : ℝ)
    (P : Finset V → ℝ) :
    AFree (Degen.eraseAtoms T.post Z) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms N (T.Y ∪ Z)) d L γ δ η C1 P := by
  obtain ⟨hA, ha, hm, ho⟩ := T.postEraseEquiv_facts Z hc hd
  exact afree_le_of_dart_equiv _ _ (T.postEraseEquiv Z hc hd) hA ha hm ho L γ δ η C1 P

theorem ladderCells_post_erase (Z : Finset V) (hc : T.c ∈ Z) (hd : T.d ∈ Z) :
    MoleProp.ladderCells (Degen.eraseAtoms T.post Z) = MoleProp.ladderCells (Degen.eraseAtoms N (T.Y ∪ Z)) := by
  obtain ⟨hA, ha, hm, ho⟩ := T.postEraseEquiv_facts Z hc hd
  exact ladderCells_eq_of_dart_equiv' _ _ (T.postEraseEquiv Z hc hd) hA ha hm ho

end TwoExit

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

/-- The new bond joins the far ends of the two exits. -/
theorem toTwoExit_cd (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) :
    ((E.toTwoExit hcap).c = M.atom (M.mate E.x) ∧ (E.toTwoExit hcap).d = M.atom (M.mate E.y)) ∨
      ((E.toTwoExit hcap).c = M.atom (M.mate E.y) ∧ (E.toTwoExit hcap).d = M.atom (M.mate E.x)) := by
  unfold toTwoExit TwoExit.c TwoExit.d
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end Y2End
end WaveTurbulence.MoleProp4

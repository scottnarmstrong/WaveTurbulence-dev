/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.LadderIrr
public import WaveTurbulence.Foundations.WaveB.Ladders
import Mathlib.Tactic

/-!
# CLASSCOUNT: the irregular darts of a molecule with disjoint ladders

For a molecule `M` of degree `≤ 4` and a family of pairwise disjoint ladders `(u_i, v_i)`, a dart is *regular* if its
atom and its mate's atom form a regular pair (rung or rail) of one of the ladders.  Interior ladder atoms have only
regular darts, the four end atoms of a ladder have at most one irregular dart each, and any other atom has at most
four darts.  Hence the number of irregular darts is at most `4 (#ladders + #free atoms)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A family of ladders of a molecule. -/
structure LadderFam (M : Molecule V D) (ι : Type) where
  len : ι → ℕ
  u : (i : ι) → Fin (len i + 1) → V
  v : (i : ι) → Fin (len i + 1) → V
  lad : ∀ i, M.IsLadder (u i) (v i)

namespace LadderFam
variable {M : Molecule V D} {ι : Type} (F : LadderFam M ι)

/-- A regular pair of the family. -/
def Reg (a b : V) : Prop := ∃ i, LReg (F.u i) (F.v i) a b

/-- The irregular darts at `a`. -/
noncomputable def irrAt (a : V) : Finset D := by
  classical
  exact (M.dartsAt a).filter (fun x => ¬ F.Reg a (M.atom (M.mate x)))

theorem card_irr_add_le (hM : M.IsMolecule) {a : V} (ha : a ∈ M.atoms) (B : Finset V) (haB : a ∉ B)
    (hB : ∀ b ∈ B, F.Reg a b) :
    (F.irrAt a).card + ∑ b ∈ B, M.bondsBetween a b ≤ 4 := by
  classical
  have hdeg := Mole.deg_le_four M hM ha
  have hsplit := Finset.card_filter_add_card_filter_not (s := M.dartsAt a)
    (fun x => M.atom (M.mate x) ∈ B)
  have hdeg' : (M.dartsAt a).card ≤ 4 := hdeg
  have h1 : (F.irrAt a).card ≤ ((M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) ∈ B)).card := by
    apply Finset.card_le_card
    intro x hx
    unfold irrAt at hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    exact hB _ h
  have h2 : ∑ b ∈ B, M.bondsBetween a b =
      ((M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ B)).card := by
    refine Eq.trans ?_ (Finset.card_eq_sum_card_fiberwise (f := fun x => M.atom (M.mate x)) (t := B)
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mp hx).2)).symm
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := fun h => haB (h ▸ hb)
    rw [Mole.bondsBetween_eq_card_darts M hab]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, h ▸ hb⟩, h⟩
    · rintro ⟨⟨hx, _⟩, h⟩; exact ⟨hx, h⟩
  omega

theorem irr_end (hM : M.IsMolecule) {a b c : V} (ha : a ∈ M.atoms) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hRb : F.Reg a b) (hRc : F.Reg a c) (h1 : M.bondsBetween a b = 2) (h2 : M.bondsBetween a c = 1) :
    (F.irrAt a).card ≤ 1 := by
  have := F.card_irr_add_le hM ha {b, c} (by simp [hab, hac]) (by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  rw [Finset.sum_pair hbc, h1, h2] at this
  omega

theorem irr_int (hM : M.IsMolecule) {a b c d : V} (ha : a ∈ M.atoms) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hRb : F.Reg a b) (hRc : F.Reg a c) (hRd : F.Reg a d) (h1 : M.bondsBetween a b = 2)
    (h2 : M.bondsBetween a c = 1) (h3 : M.bondsBetween a d = 1) :
    (F.irrAt a).card = 0 := by
  have := F.card_irr_add_le hM ha {b, c, d} (by simp [hab, hac, had]) (by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
  rw [Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_pair hcd, h1, h2, h3] at this
  omega


section atoms
variable (i : ι)

theorem inj_u {a b : Fin (F.len i + 1)} (h : F.u i a = F.u i b) : a = b := by
  have := (F.lad i).2.1 (a₁ := Sum.inl a) (a₂ := Sum.inl b) (by simpa using h)
  simpa using this

theorem inj_v {a b : Fin (F.len i + 1)} (h : F.v i a = F.v i b) : a = b := by
  have := (F.lad i).2.1 (a₁ := Sum.inr a) (a₂ := Sum.inr b) (by simpa using h)
  simpa using this

theorem ne_uv (a b : Fin (F.len i + 1)) : F.u i a ≠ F.v i b := by
  intro h
  have := (F.lad i).2.1 (a₁ := Sum.inl a) (a₂ := Sum.inr b) (by simpa using h)
  simp at this

theorem reg_uu (j jp : Fin (F.len i + 1)) (h : j.1 + 1 = jp.1) : F.Reg (F.u i j) (F.u i jp) :=
  ⟨i, LReg_rail_u_next j jp h⟩
theorem reg_uu' (j jm : Fin (F.len i + 1)) (h : jm.1 + 1 = j.1) : F.Reg (F.u i j) (F.u i jm) :=
  ⟨i, LReg_rail_u_prev j jm h⟩
theorem reg_vv (j jp : Fin (F.len i + 1)) (h : j.1 + 1 = jp.1) : F.Reg (F.v i j) (F.v i jp) :=
  ⟨i, LReg_rail_v_next j jp h⟩
theorem reg_vv' (j jm : Fin (F.len i + 1)) (h : jm.1 + 1 = j.1) : F.Reg (F.v i j) (F.v i jm) :=
  ⟨i, LReg_rail_v_prev j jm h⟩
theorem reg_uv (j : Fin (F.len i + 1)) : F.Reg (F.u i j) (F.v i j) := ⟨i, LReg_rung_u j⟩
theorem reg_vu (j : Fin (F.len i + 1)) : F.Reg (F.v i j) (F.u i j) := ⟨i, LReg_rung_v j⟩

theorem bb_uv (j : Fin (F.len i + 1)) : M.bondsBetween (F.u i j) (F.v i j) = 2 := (F.lad i).2.2.2.1 j
theorem bb_vu (j : Fin (F.len i + 1)) : M.bondsBetween (F.v i j) (F.u i j) = 2 := by
  rw [Mole.bondsBetween_symm]; exact bb_uv F i j
theorem bb_uu (j jp : Fin (F.len i + 1)) (h : j.1 + 1 = jp.1) :
    M.bondsBetween (F.u i j) (F.u i jp) = 1 := bb_u_next M (F.lad i) j jp h
theorem bb_uu' (j jm : Fin (F.len i + 1)) (h : jm.1 + 1 = j.1) :
    M.bondsBetween (F.u i j) (F.u i jm) = 1 := by
  rw [Mole.bondsBetween_symm]; exact bb_uu F i jm j h
theorem bb_vv (j jp : Fin (F.len i + 1)) (h : j.1 + 1 = jp.1) :
    M.bondsBetween (F.v i j) (F.v i jp) = 1 := bb_v_next M (F.lad i) j jp h
theorem bb_vv' (j jm : Fin (F.len i + 1)) (h : jm.1 + 1 = j.1) :
    M.bondsBetween (F.v i j) (F.v i jm) = 1 := by
  rw [Mole.bondsBetween_symm]; exact bb_vv F i jm j h

theorem irr_u (hM : M.IsMolecule) (j : Fin (F.len i + 1)) :
    (F.irrAt (F.u i j)).card ≤ (if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0) := by
  have hm : 1 ≤ F.len i := (F.lad i).1
  have ha : F.u i j ∈ M.atoms := ((F.lad i).2.2.1 j).1
  by_cases h0 : j.1 = 0
  · have hjp : (⟨1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := by simp [h0]
    have := F.irr_end hM ha (a := F.u i j) (b := F.v i j) (c := F.u i ⟨1, by omega⟩)
      (ne_uv F i _ _) (fun h => by have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega)
      (ne_uv F i _ _ |>.symm) (reg_uv F i j) (reg_uu F i j _ hjp.symm) (bb_uv F i j)
      (bb_uu F i j _ hjp.symm)
    have h2 : ¬ j.1 = F.len i := by omega
    simp [h0, h2]; omega
  · by_cases hm' : j.1 = F.len i
    · have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
      have := F.irr_end hM ha (a := F.u i j) (b := F.v i j) (c := F.u i ⟨j.1 - 1, by omega⟩)
        (ne_uv F i _ _) (fun h => by have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega)
        (ne_uv F i _ _ |>.symm) (reg_uv F i j) (reg_uu' F i j _ hjm) (bb_uv F i j)
        (bb_uu' F i j _ hjm)
      simp [h0, hm']; omega
    · have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
      have hjp : (⟨j.1 + 1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := rfl
      have := F.irr_int hM ha (a := F.u i j) (b := F.v i j) (c := F.u i ⟨j.1 - 1, by omega⟩)
        (d := F.u i ⟨j.1 + 1, by omega⟩)
        (ne_uv F i _ _) (fun h => by have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega)
        (fun h => by have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega)
        (ne_uv F i _ _ |>.symm) (ne_uv F i _ _ |>.symm)
        (fun h => by have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega)
        (reg_uv F i j) (reg_uu' F i j _ hjm) (reg_uu F i j _ hjp.symm) (bb_uv F i j)
        (bb_uu' F i j _ hjm) (bb_uu F i j _ hjp.symm)
      rw [if_neg h0, if_neg hm']; omega

theorem irr_v (hM : M.IsMolecule) (j : Fin (F.len i + 1)) :
    (F.irrAt (F.v i j)).card ≤ (if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0) := by
  have hm : 1 ≤ F.len i := (F.lad i).1
  have ha : F.v i j ∈ M.atoms := ((F.lad i).2.2.1 j).2
  by_cases h0 : j.1 = 0
  · have hjp : (⟨1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := by simp [h0]
    have := F.irr_end hM ha (a := F.v i j) (b := F.u i j) (c := F.v i ⟨1, by omega⟩)
      (ne_uv F i _ _ |>.symm) (fun h => by have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega)
      (ne_uv F i _ _) (reg_vu F i j) (reg_vv F i j _ hjp.symm) (bb_vu F i j)
      (bb_vv F i j _ hjp.symm)
    have h2 : ¬ j.1 = F.len i := by omega
    simp [h0, h2]; omega
  · by_cases hm' : j.1 = F.len i
    · have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
      have := F.irr_end hM ha (a := F.v i j) (b := F.u i j) (c := F.v i ⟨j.1 - 1, by omega⟩)
        (ne_uv F i _ _ |>.symm) (fun h => by have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega)
        (ne_uv F i _ _) (reg_vu F i j) (reg_vv' F i j _ hjm) (bb_vu F i j)
        (bb_vv' F i j _ hjm)
      simp [h0, hm']; omega
    · have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
      have hjp : (⟨j.1 + 1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := rfl
      have := F.irr_int hM ha (a := F.v i j) (b := F.u i j) (c := F.v i ⟨j.1 - 1, by omega⟩)
        (d := F.v i ⟨j.1 + 1, by omega⟩)
        (ne_uv F i _ _ |>.symm) (fun h => by have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega)
        (fun h => by have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega)
        (ne_uv F i _ _) (ne_uv F i _ _)
        (fun h => by have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega)
        (reg_vu F i j) (reg_vv' F i j _ hjm) (reg_vv F i j _ hjp.symm) (bb_vu F i j)
        (bb_vv' F i j _ hjm) (bb_vv F i j _ hjp.symm)
      rw [if_neg h0, if_neg hm']; omega


theorem sum_ite_fin (m k : ℕ) (hk : k < m + 1) :
    ∑ j : Fin (m + 1), (if j.1 = k then 1 else 0) = 1 := by
  have h : ∀ j : Fin (m + 1), (j.1 = k) ↔ (j = ⟨k, hk⟩) := fun j => by simp [Fin.ext_iff]
  simp_rw [h]
  simp

/-- The atoms of the `i`-th ladder. -/
def atomsOf (i : ι) : Finset V := Molecule.ladderAtoms (F.u i) (F.v i)

theorem sum_irr_ladder (hM : M.IsMolecule) (i : ι) :
    ∑ a ∈ F.atomsOf i, (F.irrAt a).card ≤ 4 := by
  classical
  have hm : 1 ≤ F.len i := (F.lad i).1
  unfold atomsOf Molecule.ladderAtoms
  have hdisj : Disjoint (univ.image (F.u i)) (univ.image (F.v i)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hb
    exact ne_uv F i x y hy.symm
  rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => inj_u F i h),
    Finset.sum_image (fun a _ b _ h => inj_v F i h)]
  have hu := fun j => irr_u F i hM j
  have hv := fun j => irr_v F i hM j
  calc ∑ j : Fin (F.len i + 1), (F.irrAt (F.u i j)).card + ∑ j : Fin (F.len i + 1), (F.irrAt (F.v i j)).card
      ≤ ∑ j : Fin (F.len i + 1), ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) +
        ∑ j : Fin (F.len i + 1), ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) :=
        add_le_add (Finset.sum_le_sum fun j _ => hu j) (Finset.sum_le_sum fun j _ => hv j)
    _ = 4 := by
      rw [Finset.sum_add_distrib, sum_ite_fin _ 0 (by omega), sum_ite_fin _ _ (by omega)]
      norm_num

theorem sum_irr_le (hM : M.IsMolecule) [Fintype ι] [DecidableEq ι]
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ∑ a ∈ M.atoms, (F.irrAt a).card ≤
      4 * (M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι := by
  classical
  set free := M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i) with hfree
  have hsub : M.atoms ⊆ free ∪ (univ : Finset ι).biUnion F.atomsOf := by
    intro a ha
    by_cases h : ∃ i, a ∈ F.atomsOf i
    · obtain ⟨i, hi⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · push_neg at h
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hd : Disjoint free ((univ : Finset ι).biUnion F.atomsOf) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hb
    exact (Finset.mem_filter.mp ha).2 i hi
  have hpw : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint F.atomsOf := fun i _ j _ hij => hdisj i j hij
  calc ∑ a ∈ M.atoms, (F.irrAt a).card
      ≤ ∑ a ∈ free ∪ (univ : Finset ι).biUnion F.atomsOf, (F.irrAt a).card :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ a ∈ free, (F.irrAt a).card + ∑ i : ι, ∑ a ∈ F.atomsOf i, (F.irrAt a).card := by
        rw [Finset.sum_union hd, Finset.sum_biUnion hpw]
    _ ≤ ∑ a ∈ free, 4 + ∑ i : ι, 4 := by
        refine add_le_add (Finset.sum_le_sum fun a ha => ?_) (Finset.sum_le_sum fun i _ => sum_irr_ladder F hM i)
        have ha' := (Finset.mem_filter.mp ha).1
        have h4 := Mole.deg_le_four M hM ha'
        calc (F.irrAt a).card ≤ (M.dartsAt a).card := Finset.card_filter_le _ _
          _ ≤ 4 := h4
    _ = 4 * free.card + 4 * Fintype.card ι := by simp [mul_comm]


open Classical in
/-- The irregular bonds (out darts) of the molecule. -/
theorem card_irrBonds_le (hM : M.IsMolecule) [Fintype ι] [DecidableEq ι]
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ((Finset.univ : Finset D).filter
      (fun x => M.out x = true ∧ ¬ F.Reg (M.atom x) (M.atom (M.mate x)))).card ≤
      4 * (M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι := by
  classical
  refine le_trans ?_ (sum_irr_le F hM hdisj)
  calc ((Finset.univ : Finset D).filter
        (fun x => M.out x = true ∧ ¬ F.Reg (M.atom x) (M.atom (M.mate x)))).card
      ≤ ((Finset.univ : Finset D).filter (fun x => ¬ F.Reg (M.atom x) (M.atom (M.mate x)))).card :=
        Finset.card_le_card (fun x hx => by
          rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
    _ = ∑ a ∈ M.atoms, (F.irrAt a).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := M.atom) (t := M.atoms)
          (fun x _ => Finset.mem_coe.mpr (M.atom_mem x))]
        apply Finset.sum_congr rfl
        intro a _
        unfold irrAt
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Mole.mem_dartsAt]
        constructor
        · rintro ⟨h1, h2⟩; subst h2; exact ⟨rfl, h1⟩
        · rintro ⟨h1, h2⟩; subst h1; exact ⟨h2, rfl⟩

end atoms
end LadderFam

end WaveTurbulence.ClassCount

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode2
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.ConnectedGeometryBridge
import Mathlib.Tactic

/-!
# CLASSCOUNT: bonds of a concatenation of blocks

If `S`, `T` are blocks with joints `(a, b)` and `(b, c)`, `S ∩ T = {b}` and `S ∪ T` is a block with joints `(a, c)`,
then every dart of the group `S ∪ T` belongs to exactly one of the groups `S`, `T` (`group_split`), so the arc
multiset of `S ∪ T` is the sum of those of `S` and `T` (`groupArcs_union`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem dart_in_sub (M : Molecule V D) {S U : Finset V} (hSU : S ⊆ U) {v : V}
    (hv : M.degIn U v ≤ M.degIn S v) {x : D} (hx : M.atom x = v) (hxU : M.InGroup U x) : M.InGroup S x := by
  classical
  have hsub : (M.dartsAt v).filter (M.InGroup S) ⊆ (M.dartsAt v).filter (M.InGroup U) := by
    intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨h1, h2.1 |> fun h => ⟨hSU h, hSU h2.2⟩⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by unfold Molecule.degIn at hv; exact hv)
  have hxm : x ∈ (M.dartsAt v).filter (M.InGroup U) :=
    Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M v x).mpr hx, hxU⟩
  rw [← heq] at hxm
  exact (Finset.mem_filter.mp hxm).2


/-- Darts of the union at a non-shared atom of a block lie in that block. -/
theorem dart_in_block_of_ne (M : Molecule V D) (hM : M.IsMolecule) {S U : Finset V} {j1 j2 u1 u2 : V}
    (hS : M.IsBlock S j1 j2) (hU : M.IsBlock U u1 u2) (hSU : S ⊆ U) {p : V} (hp : p ∈ S)
    (hj1 : p = j1 → j1 = u1 ∨ j1 = u2) (hj2 : p = j2 → j2 = u1 ∨ j2 = u2)
    {x : D} (hx : M.atom x = p) (hxU : M.InGroup U x) : M.InGroup S x := by
  refine dart_in_sub M hSU ?_ hx hxU
  have hdS := Mole.block_joint_degrees M hS
  have hdU := Mole.block_joint_degrees M hU
  by_cases h1 : p = j1
  · subst h1
    rcases hj1 rfl with h | h
    · rw [hdS.1]; rw [h]; rw [hdU.1]
    · rw [hdS.1]; rw [h]; rw [hdU.2]
  · by_cases h2 : p = j2
    · subst h2
      rcases hj2 rfl with h | h
      · rw [hdS.2]; rw [h]; rw [hdU.1]
      · rw [hdS.2]; rw [h]; rw [hdU.2]
    · have h4 := hS.2.2.2.2.2.2.2.2.1 p hp h1 h2
      have h5 := (Mole.degIn_le_deg M U p).trans (Mole.deg_le_four M hM (hU.1 (hSU hp)))
      omega

/-- **Concatenation of blocks splits the darts.** -/
theorem group_split (M : Molecule V D) (hM : M.IsMolecule) {S T : Finset V} {a b c : V}
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hi : S ∩ T = {b}) (x : D)
    (hx : M.InGroup (S ∪ T) x) :
    (M.InGroup S x ∧ ¬ M.InGroup T x) ∨ (M.InGroup T x ∧ ¬ M.InGroup S x) := by
  classical
  have hbS : b ∈ S := hS.2.2.1
  have hbT : b ∈ T := hT.2.1
  have hab : a ≠ b := hS.2.2.2.1
  have hbc : b ≠ c := hT.2.2.2.1
  have hloop : ¬ M.Adj b b := by
    rintro ⟨y, hy1, hy2⟩
    exact Mole.connected_degree_two_no_loop M (Molecpl.connected_to_induced M ⟨b, hbT⟩ hT.2.2.2.2.2.2.2.2.2)
      hbT hT.2.2.1 hbc.symm (Mole.block_joint_degrees M hT).1 hy1 hy2
  have hexcl : ¬ (M.InGroup S x ∧ M.InGroup T x) := by
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have e1 : M.atom x ∈ S ∩ T := Finset.mem_inter.mpr ⟨h1, h3⟩
    have e2 : M.atom (M.mate x) ∈ S ∩ T := Finset.mem_inter.mpr ⟨h2, h4⟩
    rw [hi, Finset.mem_singleton] at e1 e2
    exact hloop ⟨x, e1, e2⟩
  have hcov : M.InGroup S x ∨ M.InGroup T x := by
    have hp : M.atom x ∈ S ∪ T := hx.1
    by_cases hpb : M.atom x = b
    · -- the shared joint: degrees add up
      have hdb := degIn_add_le_union M hi hloop b
      have hdS := (Mole.block_joint_degrees M hS).2
      have hdT := (Mole.block_joint_degrees M hT).1
      have hdU : M.degIn (S ∪ T) b = 4 := hU.2.2.2.2.2.2.2.2.1 b (Finset.mem_union_left _ hbS) hab.symm hbc
      have hsub : (M.dartsAt b).filter (M.InGroup S) ∪ (M.dartsAt b).filter (M.InGroup T) ⊆
          (M.dartsAt b).filter (M.InGroup (S ∪ T)) := by
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨h1, Finset.mem_union_left _ h2.1, Finset.mem_union_left _ h2.2⟩
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨h1, Finset.mem_union_right _ h2.1, Finset.mem_union_right _ h2.2⟩
      have hdisj : Disjoint ((M.dartsAt b).filter (M.InGroup S)) ((M.dartsAt b).filter (M.InGroup T)) := by
        rw [Finset.disjoint_left]
        intro y h1 h2
        have h1' := (Finset.mem_filter.mp h1).2
        have h2' := (Finset.mem_filter.mp h2).2
        have e1 : M.atom y ∈ S ∩ T := Finset.mem_inter.mpr ⟨h1'.1, h2'.1⟩
        have e2 : M.atom (M.mate y) ∈ S ∩ T := Finset.mem_inter.mpr ⟨h1'.2, h2'.2⟩
        rw [hi, Finset.mem_singleton] at e1 e2
        exact hloop ⟨y, e1, e2⟩
      have hcard : ((M.dartsAt b).filter (M.InGroup S) ∪ (M.dartsAt b).filter (M.InGroup T)).card =
          ((M.dartsAt b).filter (M.InGroup (S ∪ T))).card := by
        rw [Finset.card_union_of_disjoint hdisj]
        have : M.degIn S b = ((M.dartsAt b).filter (M.InGroup S)).card := rfl
        have : M.degIn T b = ((M.dartsAt b).filter (M.InGroup T)).card := rfl
        have : M.degIn (S ∪ T) b = ((M.dartsAt b).filter (M.InGroup (S ∪ T))).card := rfl
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
      have hxm : x ∈ (M.dartsAt b).filter (M.InGroup (S ∪ T)) :=
        Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M b x).mpr hpb, hx⟩
      rw [← heq] at hxm
      rcases Finset.mem_union.mp hxm with h | h
      · exact Or.inl (Finset.mem_filter.mp h).2
      · exact Or.inr (Finset.mem_filter.mp h).2
    · rcases Finset.mem_union.mp hp with hpS | hpT
      · exact Or.inl (dart_in_block_of_ne M hM hS hU Finset.subset_union_left hpS
          (fun _ => Or.inl rfl) (fun h => absurd h hpb) rfl hx)
      · exact Or.inr (dart_in_block_of_ne M hM hT hU Finset.subset_union_right hpT
          (fun h => absurd h hpb) (fun _ => Or.inr rfl) rfl hx)
  tauto


theorem groupArcs_union (M : Molecule V D) (hM : M.IsMolecule) {S T : Finset V} {a b c : V}
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hi : S ∩ T = {b})
    (lab : V → ℕ) :
    groupArcs M (S ∪ T) lab = groupArcs M S lab + groupArcs M T lab := by
  classical
  unfold groupArcs
  have hdisj : Disjoint (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x)
      (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup T x) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    rcases group_split M hM hS hT hU hi x
      ⟨Finset.mem_union_left _ h1'.2.1, Finset.mem_union_left _ h1'.2.2⟩ with h | h
    · exact h.2 h2'.2
    · exact h.2 h1'.2
  have heq : (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup (S ∪ T) x) =
      (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x) ∪
      (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup T x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨ho, hx⟩
      rcases group_split M hM hS hT hU hi x hx with h | h
      · exact Or.inl ⟨ho, h.1⟩
      · exact Or.inr ⟨ho, h.1⟩
    · rintro (⟨ho, hx⟩ | ⟨ho, hx⟩)
      · exact ⟨ho, ⟨Finset.mem_union_left _ hx.1, Finset.mem_union_left _ hx.2⟩⟩
      · exact ⟨ho, ⟨Finset.mem_union_right _ hx.1, Finset.mem_union_right _ hx.2⟩⟩
  rw [heq, ← Finset.disjUnion_eq_union _ _ hdisj]
  show Multiset.map _ (_ + _) = _
  rw [Multiset.map_add]

end WaveTurbulence.ClassCount

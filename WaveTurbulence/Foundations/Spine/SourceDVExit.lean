/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceFlux
public import WaveTurbulence.Foundations.Molecule.MoleculeGroupIdentities
import Mathlib.Tactic
/-! A block meeting a double-vine-like atom set `W` (all atoms of degree four inside `W` except
two joints of degree three) and not contained in it contains both joints: group bonds leaving
the part outside `W` are balanced (flux), and each joint has at most one external dart. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem darts_inGroup_of_full (hM : M.IsMolecule) {W : Finset V} {z : V}
    (hz : z ∈ M.atoms) (hd : M.degIn W z = 4) (y : D) (hy : M.atom y = z) : M.InGroup W y := by
  have hdeg := Mole.deg_le_four M hM hz
  have he : (M.dartsAt z).filter (M.InGroup W) = M.dartsAt z :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      have : M.degIn W z = ((M.dartsAt z).filter (M.InGroup W)).card := rfl
      have h2 : M.deg z = (M.dartsAt z).card := rfl
      omega)
  have hy' : y ∈ M.dartsAt z := (Mole.mem_dartsAt M z y).mpr hy
  rw [← he] at hy'
  exact (Finset.mem_filter.mp hy').2

theorem external_dart_unique (hM : M.IsMolecule) {W : Finset V} {z : V}
    (hz : z ∈ M.atoms) (hd : M.degIn W z = 3) (y y' : D) (hy : M.atom y = z) (hy' : M.atom y' = z)
    (hny : ¬ M.InGroup W y) (hny' : ¬ M.InGroup W y') : y = y' := by
  by_contra hne
  have hdeg := Mole.deg_le_four M hM hz
  have hsub : (M.dartsAt z).filter (M.InGroup W) ∪ {y, y'} ⊆ M.dartsAt z := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact (Finset.mem_filter.mp h).1
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact (Mole.mem_dartsAt M z _).mpr hy
      · rw [Finset.mem_singleton.mp h]; exact (Mole.mem_dartsAt M z _).mpr hy'
  have hdis : Disjoint ((M.dartsAt z).filter (M.InGroup W)) {y, y'} := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    rcases Finset.mem_insert.mp ht' with rfl | h
    · exact hny (Finset.mem_filter.mp ht).2
    · rw [Finset.mem_singleton.mp h] at ht; exact hny' (Finset.mem_filter.mp ht).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_pair hne] at hc
  have h2 : M.degIn W z = ((M.dartsAt z).filter (M.InGroup W)).card := rfl
  have h3 : M.deg z = (M.dartsAt z).card := rfl
  omega

theorem block_outIn_eq (hM : M.IsMolecule) {Q : Finset V} {j1 j2 : V} (hQB : M.IsBlock Q j1 j2)
    (z : V) (hz : z ∈ Q) : M.outIn Q z = M.inIn Q z := by
  obtain ⟨hS, _, _, _, ho1, hi1, ho2, hi2, hint⟩ := hQB
  by_cases h1 : z = j1
  · subst h1; omega
  · by_cases h2 : z = j2
    · subst h2; omega
    · obtain ⟨a, b⟩ := Mole.full_oriented_counts M hM (hS hz) (hint.1 z hz h1 h2)
      omega

theorem dv_exit_contains_joints (hM : M.IsMolecule) {W Q : Finset V} {u v j1 j2 : V}
    (huv : u ≠ v) (hWu : M.degIn W u = 3) (hWv : M.degIn W v = 3)
    (hWi : ∀ z ∈ W, z ≠ u → z ≠ v → M.degIn W z = 4)
    (hQB : M.IsBlock Q j1 j2) (hQc : ∀ a ∈ Q, ∀ b ∈ Q, (Mole.induced M Q).SameComponent a b)
    (hQW : ¬ Q ⊆ W) (hne : (Q ∩ W).Nonempty) : u ∈ Q ∧ v ∈ Q := by
  have hflux := flux_balance M Q (Q \ W) Finset.sdiff_subset
    (fun z hz => block_outIn_eq M hM hQB z (Finset.mem_sdiff.mp hz).1)
  set C : Finset D := univ.filter (fun x : D => M.atom x ∈ Q \ W ∧ M.atom (M.mate x) ∈ Q \ (Q \ W))
    with hC
  have hCsplit : C.card = (univ.filter (fun x : D => M.out x = true ∧ M.atom x ∈ Q \ W ∧
      M.atom (M.mate x) ∈ Q \ (Q \ W))).card + (univ.filter (fun x : D => M.out x = false ∧
      M.atom x ∈ Q \ W ∧ M.atom (M.mate x) ∈ Q \ (Q \ W))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases h : M.out x <;> simp
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      rw [h1.1] at h2
      exact Bool.noConfusion h2.1
  -- key fact about cross darts
  have hK : ∀ x ∈ C, (M.atom (M.mate x) = u ∨ M.atom (M.mate x) = v) ∧ M.atom (M.mate x) ∈ Q := by
    intro x hx
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at hx
    obtain ⟨⟨hxQ, hxW⟩, hmQ, hmX⟩ := hx
    have hmW : M.atom (M.mate x) ∈ W := by
      by_contra h; exact hmX ⟨hmQ, h⟩
    refine ⟨?_, hmQ⟩
    by_contra hh
    push Not at hh
    have := darts_inGroup_of_full M hM (M.atom_mem _) (hWi _ hmW hh.1 hh.2) (M.mate x) rfl
    exact hxW (by simpa [Molecule.InGroup, M.mate_mate] using this.2)
  have hdistinct : ∀ x ∈ C, ∀ y ∈ C, M.atom (M.mate x) = M.atom (M.mate y) → x = y := by
    intro x hx y hy he
    have hex : ∀ t ∈ C, ¬ M.InGroup W (M.mate t) := by
      intro t ht h
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at ht
      exact ht.1.2 (by simpa [Molecule.InGroup, M.mate_mate] using h.2)
    rcases (hK x hx).1 with h1 | h1
    · have h1' : M.atom (M.mate y) = u := he ▸ h1
      have := external_dart_unique M hM (h1 ▸ M.atom_mem _) hWu (M.mate x) (M.mate y) h1 h1' (hex x hx)
        (hex y hy)
      simpa [M.mate_mate] using congrArg M.mate this
    · have h1' : M.atom (M.mate y) = v := he ▸ h1
      have := external_dart_unique M hM (h1 ▸ M.atom_mem _) hWv (M.mate x) (M.mate y) h1 h1' (hex x hx)
        (hex y hy)
      simpa [M.mate_mate] using congrArg M.mate this
  -- existence of a cross dart
  obtain ⟨a, ha, b, hb, hbn, x, hxa, hxb⟩ := Mole.connected_group_boundary M
    (Finset.inter_subset_left : Q ∩ W ⊆ Q) hne (fun h => hQW (fun t ht => (Finset.mem_inter.mp
      (h ht)).2)) hQc
  have hbQ := hb
  have hbW : b ∉ W := fun h => hbn (Finset.mem_inter.mpr ⟨hb, h⟩)
  have haQ := (Finset.mem_inter.mp ha).1
  have haW := (Finset.mem_inter.mp ha).2
  have hCmem : M.mate x ∈ C := by
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, M.mate_mate]
    refine ⟨⟨hxb ▸ hbQ, hxb ▸ hbW⟩, hxa ▸ haQ, fun h => h.2 (hxa ▸ haW)⟩
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨_, hCmem⟩
  -- balanced: the two orientation classes have equal size, so C has at least two darts
  have hcard2 : 2 ≤ C.card := by
    omega
  constructor
  · by_contra hu
    have : C.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => hdistinct x hx y hy (by
      rcases (hK x hx).1 with h | h
      · exact absurd (h ▸ (hK x hx).2) hu
      · rcases (hK y hy).1 with h' | h'
        · exact absurd (h' ▸ (hK y hy).2) hu
        · rw [h, h'])
    omega
  · by_contra hv
    have : C.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => hdistinct x hx y hy (by
      rcases (hK x hx).1 with h | h
      · rcases (hK y hy).1 with h' | h'
        · rw [h, h']
        · exact absurd (h' ▸ (hK y hy).2) hv
      · exact absurd (h ▸ (hK x hx).2) hv)
    omega

end WaveTurbulence.LGSpine

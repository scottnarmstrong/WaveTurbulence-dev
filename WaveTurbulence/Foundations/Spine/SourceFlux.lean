/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockSameJoints
public import WaveTurbulence.Foundations.Spine.MoleculeOrientationUnion
import Mathlib.Tactic
/-! Flux balance for a group: if every atom of `X ⊆ S` has equally many outgoing and incoming
bonds inside the group `S`, then as many group bonds leave `X` (into `S \ X`) as enter it. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem sum_outIn_eq_card (S X : Finset V) (b : Bool) :
    ∑ z ∈ X, ((M.dartsAt z).filter (fun x => M.InGroup S x ∧ M.out x = b)).card =
      (univ.filter (fun x : D => M.out x = b ∧ M.InGroup S x ∧ M.atom x ∈ X)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := M.atom) (t := X)]
  · refine Finset.sum_congr rfl fun z hz => ?_
    congr 1
    ext x
    simp [Molecule.dartsAt]
    constructor
    · rintro ⟨hx, hg, ho⟩; exact ⟨⟨ho, hg, hx ▸ hz⟩, hx⟩
    · rintro ⟨⟨ho, hg, _⟩, hx⟩; exact ⟨hx, hg, ho⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact hx.2.2.2

theorem flux_balance (S X : Finset V) (hXS : X ⊆ S)
    (h : ∀ z ∈ X, M.outIn S z = M.inIn S z) :
    (univ.filter (fun x : D => M.out x = true ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X)).card =
    (univ.filter (fun x : D => M.out x = false ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X)).card := by
  have hsum : (univ.filter (fun x : D => M.out x = true ∧ M.InGroup S x ∧ M.atom x ∈ X)).card =
      (univ.filter (fun x : D => M.out x = false ∧ M.InGroup S x ∧ M.atom x ∈ X)).card := by
    rw [← sum_outIn_eq_card M S X true, ← sum_outIn_eq_card M S X false]
    exact Finset.sum_congr rfl h
  have split : ∀ b : Bool,
      (univ.filter (fun x : D => M.out x = b ∧ M.InGroup S x ∧ M.atom x ∈ X)).card =
      (univ.filter (fun x : D => M.out x = b ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ X)).card +
      (univ.filter (fun x : D => M.out x = b ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X)).card := by
    intro b
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
      unfold Molecule.InGroup
      constructor
      · rintro ⟨ho, ⟨h1, h2⟩, h3⟩
        by_cases hm : M.atom (M.mate x) ∈ X
        · exact Or.inl ⟨ho, h3, hm⟩
        · exact Or.inr ⟨ho, h3, h2, hm⟩
      · rintro (⟨ho, h3, hm⟩ | ⟨ho, h3, h2, hm⟩)
        · exact ⟨ho, ⟨hXS h3, hXS hm⟩, h3⟩
        · exact ⟨ho, ⟨hXS h3, h2⟩, h3⟩
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      exact (Finset.mem_sdiff.mp h2.2.2).2 h1.2.2
  have hint : (univ.filter (fun x : D => M.out x = true ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ X)).card =
      (univ.filter (fun x : D => M.out x = false ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∈ X)).card := by
    apply Finset.card_bij (fun x _ => M.mate x)
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [M.out_mate, hx.1, M.mate_mate]
      exact ⟨rfl, hx.2.2, hx.2.1⟩
    · intro x _ y _ he
      simpa [M.mate_mate] using congrArg M.mate he
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      refine ⟨M.mate y, ?_, M.mate_mate y⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [M.out_mate, hy.1, M.mate_mate]
      exact ⟨rfl, hy.2.2, hy.2.1⟩
  have h1 := split true
  have h2 := split false
  omega

end WaveTurbulence.LGSpine

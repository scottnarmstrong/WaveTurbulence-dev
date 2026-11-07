/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
import Mathlib.Tactic

/-! # Old degree exhaustion turns a finite endpoint table into a complete atomic group -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem table_edge_incidence (M : Molecule V D) (P : AppbPattern)
    (f : ℕ → V) (hf : Set.InjOn f (P.vertices : Set ℕ))
    (edge : Fin P.edges.length → D)
    (hend : ∀ i,M.ends (edge i) = s(f P.edges[i].1,f P.edges[i].2))
    (i : Fin P.edges.length) (a : ℕ) (ha : a ∈ P.vertices) :
    appbIncidence M (f a) (edge i) =
      (if P.edges[i].1 = a then 1 else 0)+(if P.edges[i].2 = a then 1 else 0) := by
  have hl : f P.edges[i].1 = f a ↔ P.edges[i].1 = a :=
    ⟨fun he => hf (P.edge_fst_mem i) ha he,congrArg f⟩
  have hr : f P.edges[i].2 = f a ↔ P.edges[i].2 = a :=
    ⟨fun he => hf (P.edge_snd_mem i) ha he,congrArg f⟩
  rcases Sym2.eq_iff.mp (hend i) with h | h
  · simp only [appbIncidence,h.1,h.2,hl,hr]
  · simp only [appbIncidence,h.1,h.2,hl,hr]
    omega

theorem table_selected_incidence_sum (M : Molecule V D) (P : AppbPattern)
    (f : ℕ → V) (hf : Set.InjOn f (P.vertices : Set ℕ))
    (edge : Fin P.edges.length → D) (he : Function.Injective edge)
    (hend : ∀ i,M.ends (edge i) = s(f P.edges[i].1,f P.edges[i].2))
    (a : ℕ) (ha : a ∈ P.vertices) :
    (∑ x ∈ univ.image edge,appbIncidence M (f a) x) = P.localDegree a := by
  rw [sum_image he.injOn]
  apply sum_congr rfl
  intro i hi
  exact table_edge_incidence M P f hf edge hend i a ha

theorem table_covers_removed_bond (M : Molecule V D) (P : AppbPattern)
    (f : ℕ → V) (hf : Set.InjOn f (P.vertices : Set ℕ))
    (edge : Fin P.edges.length → D) (he : Function.Injective edge)
    (hout : ∀ i,M.out (edge i) = true)
    (hend : ∀ i,M.ends (edge i) = s(f P.edges[i].1,f P.edges[i].2))
    (hdeg : ∀ a ∈ P.removed,M.deg (f a) = P.localDegree a)
    {x : D} (hx : x ∈ appbRemovedBonds M (P.removed.image f)) : x ∈ univ.image edge := by
  classical
  obtain ⟨hxout,hinc⟩ := mem_filter.mp hx
  obtain ⟨a,ha,hax⟩ : ∃ a ∈ P.removed,M.atom x = f a ∨ M.atom (M.mate x) = f a := by
    rcases hinc with h | h
    · obtain ⟨a,ha,he⟩ := mem_image.mp h
      exact ⟨a,ha,Or.inl he.symm⟩
    · obtain ⟨a,ha,he⟩ := mem_image.mp h
      exact ⟨a,ha,Or.inr he.symm⟩
  have hsum : (∑ y ∈ univ.image edge,appbIncidence M (f a) y) = M.deg (f a) :=
    (table_selected_incidence_sum M P f hf edge he hend a (mem_union_left _ ha)).trans (hdeg a ha).symm
  have hpos : 1 ≤ appbIncidence M (f a) x := by
    rcases hax with h | h
    · simp only [appbIncidence,h,ite_true]
      omega
    · simp only [appbIncidence,h,ite_true]
      omega
  by_contra hn
  have hsub : insert x (univ.image edge) ⊆ M.bonds := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hxout
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact mem_filter.mpr ⟨mem_univ _,hout i⟩
  have hle : (∑ y ∈ insert x (univ.image edge),appbIncidence M (f a) y) ≤ M.deg (f a) := by
    rw [appb_degree_bond_sum]
    exact sum_le_sum_of_subset_of_nonneg hsub (by intro y hy hn; exact Nat.zero_le _)
  rw [sum_insert hn,hsum] at hle
  omega

end WaveTurbulence.Mole.AppbAlgorithm

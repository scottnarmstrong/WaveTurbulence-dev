/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapBonds
public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
import Mathlib.Tactic

/-! # Actual and literal cap bond endpoints stay in their finite atom support -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Every literal cap bond joins two available cap labels. -/
theorem capBonds_endpoints_mem (N r : ℕ) : ∀ e ∈ capBonds N r,
    e.1 ∈ capLabels N r ∧ e.2 ∈ capLabels N r := by
  have hold (a : ℕ) (ha : a=4 ∨ a=5 ∨ a=6) : a ∈ capLabels N r :=
    (mem_capLabels_iff N r a).mpr (by omega)
  have hu : ∀ w ∈ (List.range r).map (N+·),w ∈ capLabels N r := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    rw [mem_capLabels_iff]
    omega
  have hv : ∀ w ∈ (List.range r).map (N+r+·),w ∈ capLabels N r := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    rw [mem_capLabels_iff]
    omega
  have hrail (a : ℕ) (ws : List ℕ) (ha : a ∈ capLabels N r)
      (hw : ∀ w ∈ ws,w ∈ capLabels N r) : ∀ e ∈ openRailBonds a ws,
      e.1 ∈ capLabels N r ∧ e.2 ∈ capLabels N r := by
    intro e he
    have hh := List.of_mem_zip he
    constructor
    · rcases List.mem_cons.mp hh.1 with h | h
      · exact h ▸ ha
      · exact hw _ h
    · exact hw _ hh.2
  intro e he
  simp only [capBonds,List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [capTriangleBonds,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> constructor <;> apply hold <;> omega
  · exact hrail 5 _ (hold 5 (by omega)) hu e he
  · exact hrail 6 _ (hold 6 (by omega)) hv e he
  · obtain ⟨i,hi,rfl⟩ := allocatedRungs_mem he
    constructor <;> rw [mem_capLabels_iff] <;> omega

/-- The undirected raw cap multiset has no atom outside its exact label set. -/
theorem capBondMultiset_support (N r : ℕ) :
    ∀ e ∈ rawBondMultiset (capBonds N r),∀ a ∈ e,a ∈ capLabels N r := by
  intro e he a ha
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
  have hh := capBonds_endpoints_mem N r p hp
  rcases Sym2.mem_iff.mp ha with h | h
  · exact h ▸ hh.1
  · exact h ▸ hh.2

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Mapping actual induced bonds never leaves the image of the actual atoms. -/
theorem mapped_groupBonds_support (M : Molecule V D) (A : Finset V) (f : V → ℕ) :
    ∀ e ∈ (M.groupBonds A).map (Sym2.map f),∀ a ∈ e,a ∈ A.image f := by
  intro e he a ha
  simp only [Molecule.groupBonds,Multiset.map_map,Multiset.mem_map,
    mem_val,mem_filter,mem_univ,true_and,Function.comp_apply] at he
  obtain ⟨d,⟨_hout,hg⟩,rfl⟩ := he
  simp only [Molecule.ends,Sym2.map_mk,Sym2.mem_iff] at ha
  rcases ha with h | h
  · exact h ▸ mem_image_of_mem f hg.1
  · exact h ▸ mem_image_of_mem f hg.2

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FiniteImages
import Mathlib.Tactic

/-! # The actual removed half-edges are covered by four or five source labels -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem deleted_cover_of_incident_cover (M : Molecule V D) (Y : Finset V)
    {r : ℕ} (e : Fin r → D)
    (hAt : ∀ z : D, M.atom z ∈ Y → ∃ i, z = e i ∨ z = M.mate (e i)) :
    ∀ z : DeletedDart M Y, ∃ i, z.val = e i ∨ z.val = M.mate (e i) := by
  intro z
  by_cases hz : M.atom z.val ∈ Y
  · exact hAt z.val hz
  · have hmz : M.atom (M.mate z.val) ∈ Y := by
      by_contra h
      exact z.property ⟨hz,h⟩
    obtain ⟨i,hi | hi⟩ := hAt (M.mate z.val) hmz
    · refine ⟨i,Or.inr ?_⟩
      have hh := congrArg M.mate hi
      simpa only [M.mate_mate] using hh
    · exact ⟨i,Or.inl (Mole.mate_injective M hi)⟩

theorem deleted_pair_coverage_three_three (M : Molecule V D) {a b : V} {x y r s : D}
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s}) :
    ∀ z : DeletedDart M {a,b}, ∃ i : Fin 4,
      z.val = (![x,y,r,s] : Fin 4 → D) i ∨ z.val = M.mate ((![x,y,r,s] : Fin 4 → D) i) := by
  apply deleted_cover_of_incident_cover
  intro z hz
  rcases mem_insert.mp hz with hz | hz
  · have hmem : z ∈ M.dartsAt a := (Mole.mem_dartsAt M a z).mpr hz
    rw [hA] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inl hzx⟩
    · rcases mem_insert.mp hmem with hzy | hzr
      · exact ⟨1,Or.inl hzy⟩
      · exact ⟨2,Or.inl (mem_singleton.mp hzr)⟩
  · have hzb : M.atom z = b := mem_singleton.mp hz
    have hmem : z ∈ M.dartsAt b := (Mole.mem_dartsAt M b z).mpr hzb
    rw [hB] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inr hzx⟩
    · rcases mem_insert.mp hmem with hzy | hzs
      · exact ⟨1,Or.inr hzy⟩
      · exact ⟨3,Or.inl (mem_singleton.mp hzs)⟩

theorem deleted_pair_coverage_three_four (M : Molecule V D) {a b : V} {x y r s t : D}
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s,t}) :
    ∀ z : DeletedDart M {a,b}, ∃ i : Fin 5,
      z.val = (![x,y,r,s,t] : Fin 5 → D) i ∨ z.val = M.mate ((![x,y,r,s,t] : Fin 5 → D) i) := by
  apply deleted_cover_of_incident_cover
  intro z hz
  rcases mem_insert.mp hz with hz | hz
  · have hmem : z ∈ M.dartsAt a := (Mole.mem_dartsAt M a z).mpr hz
    rw [hA] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inl hzx⟩
    · rcases mem_insert.mp hmem with hzy | hzr
      · exact ⟨1,Or.inl hzy⟩
      · exact ⟨2,Or.inl (mem_singleton.mp hzr)⟩
  · have hzb : M.atom z = b := mem_singleton.mp hz
    have hmem : z ∈ M.dartsAt b := (Mole.mem_dartsAt M b z).mpr hzb
    rw [hB] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inr hzx⟩
    · rcases mem_insert.mp hmem with hzy | hmem
      · exact ⟨1,Or.inr hzy⟩
      · rcases mem_insert.mp hmem with hzs | hzt
        · exact ⟨3,Or.inl hzs⟩
        · exact ⟨4,Or.inl (mem_singleton.mp hzt)⟩

end WaveTurbulence.MoleProp

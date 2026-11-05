/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideBonds
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
import Mathlib.Tactic

/-! # Every raw side bond has both endpoints in the exact side label set -/

public section
namespace WaveTurbulence.Vine

/-- A rail whose vertices all lie in W has both endpoints of every bond in W. -/
theorem railBonds_endpoints_mem (W : Finset ℕ) (a b : ℕ) (ws : List ℕ)
    (ha : a ∈ W) (hb : b ∈ W) (hws : ∀ w ∈ ws,w ∈ W) :
    ∀ e ∈ railBonds a ws b,e.1 ∈ W ∧ e.2 ∈ W := by
  intro e he
  have hh := List.of_mem_zip he
  constructor
  · rcases List.mem_cons.mp hh.1 with h | h
    · exact h ▸ ha
    · exact hws _ h
  · rcases List.mem_append.mp hh.2 with h | h
    · exact hws _ h
    · exact List.mem_singleton.mp h ▸ hb

/-- All literal side bond endpoints are available side labels, for every
nonnegative number of interior full rungs. -/
theorem sideBonds_endpoints_mem (N k : ℕ) : ∀ e ∈ sideBonds N k,
    e.1 ∈ sideLabels N k ∧ e.2 ∈ sideLabels N k := by
  intro e he
  have h4 : 4 ∈ sideLabels N k := (mem_sideLabels_iff N k 4).mpr (by omega)
  have h5 : 5 ∈ sideLabels N k := (mem_sideLabels_iff N k 5).mpr (by omega)
  have h6 : 6 ∈ sideLabels N k := (mem_sideLabels_iff N k 6).mpr (by omega)
  have h7 : 7 ∈ sideLabels N k := (mem_sideLabels_iff N k 7).mpr (by omega)
  have h8 : 8 ∈ sideLabels N k := (mem_sideLabels_iff N k 8).mpr (by omega)
  have hu : ∀ w ∈ (List.range k).map (N+·),w ∈ sideLabels N k := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    rw [mem_sideLabels_iff]
    omega
  have hv : ∀ w ∈ (List.range k).map (N+k+·),w ∈ sideLabels N k := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    rw [mem_sideLabels_iff]
    omega
  simp only [sideBonds,List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by assumption,by assumption⟩
  · exact railBonds_endpoints_mem _ _ _ _ h5 h7 hu e he
  · exact railBonds_endpoints_mem _ _ _ _ h6 h8 hv e he
  · obtain ⟨i,hi,rfl⟩ := allocatedRungs_mem he
    constructor <;> rw [mem_sideLabels_iff] <;> omega

end WaveTurbulence.Vine

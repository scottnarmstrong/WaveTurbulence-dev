/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungNeighbors
import Mathlib.Tactic

/-! # Restrict literal bond lists to selected endpoint labels -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Keep exactly those literal edges whose two endpoints are selected. -/
@[expose] def restrictBonds (W : Finset ℕ) (es : List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  es.filter (fun e => decide (e.1 ∈ W ∧ e.2 ∈ W))

/-- Restriction commutes with concatenating bond lists. -/
theorem restrictBonds_append (W : Finset ℕ) (es fs : List (ℕ×ℕ)) :
    restrictBonds W (es++fs)=restrictBonds W es++restrictBonds W fs := List.filter_append es fs

/-- Restriction commutes with erasing one copy of a specified bond. -/
theorem restrictBonds_erase (W : Finset ℕ) (es : List (ℕ×ℕ)) (e : ℕ×ℕ) :
    restrictBonds W (es.erase e)=(restrictBonds W es).erase e := List.erase_filter.symm

/-- Erasing a nonselected bond does not change the selected graph. -/
theorem restrictBonds_erase_external (W : Finset ℕ) (es : List (ℕ×ℕ)) (e : ℕ×ℕ)
    (he : ¬(e.1 ∈ W ∧ e.2 ∈ W)) : restrictBonds W (es.erase e)=restrictBonds W es := by
  rw [restrictBonds_erase]
  apply List.erase_of_not_mem
  intro hm
  have hh := (List.mem_filter.mp hm).2
  simp only [decide_eq_true_eq] at hh
  exact he hh

/-- A rail with no selected interior atom and no selected endpoint pair
contributes no selected edge, including the empty-interior convention. -/
theorem restrictBonds_rail_empty (W : Finset ℕ) (a b : ℕ) (ws : List ℕ)
    (hw : ∀ w ∈ ws,w ∉ W) (hab : ¬(a ∈ W ∧ b ∈ W)) :
    restrictBonds W (railBonds a ws b)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he hp
  have hp' : e.1 ∈ W ∧ e.2 ∈ W := by simpa only [decide_eq_true_eq] using hp
  have hh := List.of_mem_zip he
  rcases List.mem_cons.mp hh.1 with ha | hi
  · rcases List.mem_append.mp hh.2 with hi | hb
    · exact hw _ hi hp'.2
    · exact hab ⟨ha ▸ hp'.1,List.mem_singleton.mp hb ▸ hp'.2⟩
  · exact hw _ hi hp'.1

/-- A rail with every atom selected is unchanged by restriction. -/
theorem restrictBonds_rail_full (W : Finset ℕ) (a b : ℕ) (ws : List ℕ)
    (ha : a ∈ W) (hb : b ∈ W) (hw : ∀ w ∈ ws,w ∈ W) :
    restrictBonds W (railBonds a ws b)=railBonds a ws b := by
  apply List.filter_eq_self.mpr
  intro e he
  have hh := List.of_mem_zip he
  apply decide_eq_true
  constructor
  · rcases List.mem_cons.mp hh.1 with he | he
    · exact he.symm ▸ ha
    · exact hw _ he
  · rcases List.mem_append.mp hh.2 with he | he
    · exact hw _ he
    · exact (List.mem_singleton.mp he).symm ▸ hb

/-- Doubled fresh rungs disappear if their upper atoms are all outside. -/
theorem restrictBonds_rungs_empty (W : Finset ℕ) (N P k : ℕ)
    (hN : ∀ i<k,N+i ∉ W) : restrictBonds W (allocatedRungs N P k)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he hp
  obtain ⟨i,hi,rfl⟩ := allocatedRungs_mem he
  have hh : N+i ∈ W ∧ P+i ∈ W := by simpa only [decide_eq_true_eq] using hp
  exact hN i hi hh.1

/-- Doubled fresh rungs remain when both allocated rails are selected. -/
theorem restrictBonds_rungs_full (W : Finset ℕ) (N P k : ℕ)
    (hN : ∀ i<k,N+i ∈ W) (hP : ∀ i<k,P+i ∈ W) :
    restrictBonds W (allocatedRungs N P k)=allocatedRungs N P k := by
  apply List.filter_eq_self.mpr
  intro e he
  obtain ⟨i,hi,rfl⟩ := allocatedRungs_mem he
  exact decide_eq_true ⟨hN i hi,hP i hi⟩

end WaveTurbulence.Vine

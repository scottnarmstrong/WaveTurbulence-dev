/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Vine and ladder coherence (TARGET cohmol)

The group list comes from the chosen template realization. Layers take values
in any type with decidable equality; natural-number layers are a special case.
-/

public section
namespace WaveTurbulence.Vine

variable {A L : Type*} [DecidableEq L]

/-- All atoms in one group have the same layer. Empty groups satisfy this;
actual vine groups have two or three atoms. -/
@[expose] def GroupCoherent (layer : A → L) (g : List A) : Prop :=
  ∀ x ∈ g, ∀ y ∈ g, layer x = layer y

instance (layer : A → L) (g : List A) : Decidable (GroupCoherent layer g) := by
  unfold GroupCoherent
  infer_instance

/-- TARGET cohmol: the number of groups with unequal layers. -/
@[expose] def incoherencyIndex (layer : A → L) (groups : List (List A)) : ℕ :=
  (groups.filter fun g => ¬ GroupCoherent layer g).length

/-- TARGET cohmol: each group is contained in a single layer. -/
@[expose] def Coherent (layer : A → L) (groups : List (List A)) : Prop :=
  ∀ g ∈ groups, GroupCoherent layer g

/-- Coherence is exactly vanishing incoherency index. -/
theorem incoherencyIndex_eq_zero_iff (layer : A → L) (groups : List (List A)) :
    incoherencyIndex layer groups = 0 ↔ Coherent layer groups := by
  simp only [incoherencyIndex,List.length_eq_zero_iff,List.filter_eq_nil_iff,
    decide_eq_true_eq,not_not,Coherent]

/-- The index never exceeds the number of groups. -/
theorem incoherencyIndex_le (layer : A → L) (groups : List (List A)) :
    incoherencyIndex layer groups ≤ groups.length := List.length_filter_le _ _

/-- Concatenating group lists adds the indices. -/
theorem incoherencyIndex_append (layer : A → L) (g h : List (List A)) :
    incoherencyIndex layer (g++h) = incoherencyIndex layer g + incoherencyIndex layer h := by
  simp only [incoherencyIndex,List.filter_append,List.length_append]

/-- A rung contributes exactly one when its two layers differ. -/
theorem incoherencyIndex_rung (layer : A → L) (a b : A) :
    incoherencyIndex layer [[a,b]] = if layer a = layer b then 0 else 1 := by
  by_cases h : layer a = layer b
  · simp [incoherencyIndex,GroupCoherent,h]
  · simp [incoherencyIndex,GroupCoherent,h]

omit [DecidableEq L] in
/-- Type I has no groups and is coherent for every layering. -/
theorem typeI_coherent (layer : ℕ → L) : Coherent layer VineType.I.template.groups := by
  simp [Coherent,VineType.template]

/-- TARGET cohmol: ladder groups are exactly its paired rung atoms. -/
@[expose] def ladderGroups {m : ℕ} (u v : Fin (m+1) → A) : List (List A) :=
  (List.finRange (m+1)).map fun j => [u j,v j]

omit [DecidableEq L] in
/-- A ladder is coherent precisely when the two atoms of every rung agree. -/
theorem ladder_coherent_iff {m : ℕ} (layer : A → L) (u v : Fin (m+1) → A) :
    Coherent layer (ladderGroups u v) ↔ ∀ j, layer (u j) = layer (v j) := by
  simp [Coherent,ladderGroups,GroupCoherent,eq_comm]

/-- A ladder of length m has incoherency index at most m+1. -/
theorem ladder_index_le {m : ℕ} (layer : A → L) (u v : Fin (m+1) → A) :
    incoherencyIndex layer (ladderGroups u v) ≤ m+1 := by
  simpa only [ladderGroups,List.length_map,List.length_finRange] using
    incoherencyIndex_le layer (ladderGroups u v)

end WaveTurbulence.Vine

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Exists
import Mathlib.Tactic

/-!
# TARGET vinechainlem (L1930-L1933, DH23 Lemma 8.1): existence and uniqueness

For every molecule there is a unique collection of disjoint atomic groups, each an HV, VC, HVC or
DV, such that every designated vine-like object is contained in one of them.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isVineLikeSet_subset_atoms {S : Finset V} (h : IsVineLikeSet M S) : S ⊆ M.atoms := by
  obtain ⟨P, rfl⟩ := object_of_isVineLikeSet h
  obtain ⟨⟨R⟩, _, _⟩ := object_overlap_premises P
  exact R.atoms_subset

theorem exists_maxVL_above {S0 : Finset V} (h : IsVineLikeSet M S0) :
    ∃ T ∈ maxVL M, S0 ⊆ T := by
  classical
  let s : Finset (Finset V) := M.atoms.powerset.filter (fun T => IsVineLikeSet M T ∧ S0 ⊆ T)
  have hne : s.Nonempty :=
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (isVineLikeSet_subset_atoms h), h, subset_rfl⟩⟩
  obtain ⟨m, hmmax⟩ := Finset.exists_maximal hne
  have hm := hmmax.1
  have hm' := Finset.mem_filter.mp hm
  refine ⟨m, ⟨hm'.2.1, fun T' hT' hmT' => ?_⟩, hm'.2.2⟩
  have hTs : T' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (isVineLikeSet_subset_atoms hT'),
    hT', hm'.2.2.trans hmT'⟩
  exact Finset.Subset.antisymm (hmmax.2 hTs hmT') hmT'

theorem stage1Collection_isPartition (hM : M.IsMolecule) :
    IsSourceVinePartition M (stage1Collection M) := by
  refine ⟨fun S hS => stage1Collection_isGroup hM hS, stage1Collection_disjoint hM, fun P => ?_⟩
  obtain ⟨X, hX, hPX⟩ := exists_maxVL_above (isVineLikeSet_of_object P)
  by_cases hiso : ∀ T ∈ maxVL M, T ≠ X → Disjoint X T
  · exact ⟨X, Or.inl ⟨hX, hiso⟩, hPX⟩
  · push Not at hiso
    obtain ⟨T, hT, hTX, hnd⟩ := hiso
    exact ⟨X ∪ T, Or.inr ⟨X, hX, T, hT, Ne.symm hTX, hnd, rfl⟩, hPX.trans subset_union_left⟩

/-- **TARGET vinechainlem (L1930-L1933; DH23 Lemma 8.1).** For any molecule there is a unique
collection of disjoint atomic groups, each an HV, VC, HVC or DV, such that every designated
vine-like object is contained in one of them. -/
theorem vinechainlem (hM : M.IsMolecule) : ∃! C : Set (Finset V), IsSourceVinePartition M C :=
  ⟨stage1Collection M, stage1Collection_isPartition hM, fun _ hC => partition_unique hC (stage1Collection_isPartition hM)⟩

end WaveTurbulence.Stage1

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Exact leaf decomposition at the three ordered child slots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem mem_leafAddresses_node3 {w : ℕ} (f : Fin 3 → TTree) (a z : Address w) :
    z ∈ leafAddresses (node3 f) a ↔ ∃ i : Fin 3, z ∈ leafAddresses (f i) (addrExt a [i]) := by
  rw [node3,leafAddresses_node]
  simp only [Finset.mem_union]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

end WaveTurbulence.Reg.Skeleton

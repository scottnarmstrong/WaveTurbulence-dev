/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeTransport
import Mathlib.Tactic

/-! # Cells of the merged molecule away from the merged atom

A ladder cell of `mergePair M v₁ v₂` avoiding `v₁` is a ladder cell of `M` avoiding `{v₁, v₂}`, with the same gaps.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

theorem atom_N_iff (z : OffPair M v₁ v₂) {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).atom z = y ↔ M.atom z.val = y := by
  rw [Merge.atom_eq]
  by_cases hz : M.atom z.val = v₂
  · rw [hz, mergeMap, if_pos rfl]; exact ⟨fun h => absurd h.symm h1, fun h => absurd h.symm h2⟩
  · rw [Merge.mergeMap_of_ne hz]

theorem directed_merge_far {a b : V} (ha1 : a ≠ v₁) (ha2 : a ≠ v₂) (hb1 : b ≠ v₁) (hb2 : b ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨z, hz, hza, hzb⟩
    refine ⟨z.val, hz, (atom_N_iff z ha1 ha2).mp hza, ?_⟩
    have := (atom_N_iff (hv₁ := hv₁) (hne := hne) ((mergePair M v₁ v₂ hv₁ hne).mate z) hb1 hb2).mp hzb
    exact this
  · rintro ⟨x, hx, hxa, hxb⟩
    have hoff : M.ends x ≠ s(v₁, v₂) := by
      intro h
      have hm : M.atom x ∈ M.ends x := Sym2.mem_mk_left _ _
      rw [h, hxa] at hm
      rcases Sym2.mem_iff.mp hm with h' | h'
      · exact ha1 h'
      · exact ha2 h'
    refine ⟨⟨x, hoff⟩, hx, (atom_N_iff ⟨x, hoff⟩ ha1 ha2).mpr hxa, ?_⟩
    exact (atom_N_iff (hv₁ := hv₁) (hne := hne) ((mergePair M v₁ v₂ hv₁ hne).mate ⟨x, hoff⟩) hb1 hb2).mpr hxb

theorem sourceLadder_merge_iff {m : ℕ} (u v : Fin (m + 1) → V)
    (hnot : ∀ j, u j ≠ v₁ ∧ u j ≠ v₂ ∧ v j ≠ v₁ ∧ v j ≠ v₂) :
    Degen.SourceLadder (mergePair M v₁ v₂ hv₁ hne) u v ↔ Degen.SourceLadder M u v := by
  have hatoms : (∀ j, u j ∈ (mergePair M v₁ v₂ hv₁ hne).atoms ∧ v j ∈ (mergePair M v₁ v₂ hv₁ hne).atoms) ↔
      (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) := by
    constructor
    · intro h j
      exact ⟨(mem_erase.mp (h j).1).2, (mem_erase.mp (h j).2).2⟩
    · intro h j
      exact ⟨mem_erase.mpr ⟨(hnot j).2.1, (h j).1⟩, mem_erase.mpr ⟨(hnot j).2.2.2, (h j).2⟩⟩
  unfold Degen.SourceLadder
  rw [hatoms]
  simp_rw [Merge.bondsBetween_far (hv₁ := hv₁) (hne := hne) (hnot _).1 (hnot _).2.1 (hnot _).2.2.1 (hnot _).2.2.2,
    Merge.bondsBetween_far (hv₁ := hv₁) (hne := hne) (hnot _).1 (hnot _).2.1 (hnot _).1 (hnot _).2.1,
    Merge.bondsBetween_far (hv₁ := hv₁) (hne := hne) (hnot _).2.2.1 (hnot _).2.2.2 (hnot _).2.2.1 (hnot _).2.2.2,
    directed_merge_far (hv₁ := hv₁) (hne := hne) (hnot _).1 (hnot _).2.1 (hnot _).1 (hnot _).2.1,
    directed_merge_far (hv₁ := hv₁) (hne := hne) (hnot _).2.2.1 (hnot _).2.2.2 (hnot _).2.2.1 (hnot _).2.2.2]

end MergeSum
end WaveTurbulence.FinalCountG8

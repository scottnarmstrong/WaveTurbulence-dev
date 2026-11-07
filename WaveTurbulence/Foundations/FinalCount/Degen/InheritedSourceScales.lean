/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
public import WaveTurbulence.Foundations.FinalCount.WorldSelectedLadderDisjoint
public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
import Mathlib.Tactic

/-! # Literal transported ladder scales for actual post-removal maximal ladders -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sourceLadderSet_nonempty (M : Molecule V D) {S : Finset V} (hS : SourceLadderSet M S) :
    S.Nonempty := by
  obtain ⟨m, u, v, _hL, rfl⟩ := hS
  refine ⟨u 0, ?_⟩
  exact mem_union_left _ (mem_image_of_mem u (mem_univ _))

/-- Every actual new maximal ladder has exactly one old maximal parent. -/
theorem existsUnique_source_parent (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) {T : Finset V} (hT : T ∈ sourceMaximalLadders (eraseAtoms M Y)) :
    ∃! S : Finset V, S ∈ sourceMaximalLadders M ∧ T ⊆ S := by
  classical
  have hTpost : SourceLadderSet (eraseAtoms M Y) T := (mem_filter.mp hT).2.1
  have hTold := ((sourceLadderSet_erase_iff M Y T).mp hTpost).1
  obtain ⟨S, hS, hTS⟩ := exists_sourceMaximalLadder_superset M hTold
  refine ⟨S, ⟨hS, hTS⟩, ?_⟩
  intro S' hS'
  by_contra hne
  have hpair := sourceMaximalLadders_pairwiseDisjoint M hM
  have hd : Disjoint S' S := hpair hS'.1 hS hne
  obtain ⟨x, hx⟩ := sourceLadderSet_nonempty M hTold
  exact (disjoint_left.mp hd) (hS'.2 hx) (hTS hx)

/-- A finite explicit parameter extension: on a new maximal ladder the
sum has exactly its unique old parent term. Outside the used family this
is simply the same literal finite sum, not a chosen/fallback source object. -/
noncomputable def inheritedSourceScale (M : Molecule V D) (P : Finset V → ℝ) (T : Finset V) : ℝ := by
  classical
  exact ∑ S ∈ (sourceMaximalLadders M).filter (fun S => T ⊆ S), P S

theorem inheritedSourceScale_nonneg (M : Molecule V D) (P : Finset V → ℝ)
    (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) (T : Finset V) :
    0 ≤ inheritedSourceScale M P T := by
  classical
  unfold inheritedSourceScale
  apply sum_nonneg
  intro S hS
  exact hP S (mem_filter.mp hS).1

/-- Transport is exactly the original scale at the actual old parent. -/
theorem inheritedSourceScale_eq_parent (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) (P : Finset V → ℝ) {T S : Finset V}
    (hT : T ∈ sourceMaximalLadders (eraseAtoms M Y))
    (hS : S ∈ sourceMaximalLadders M) (hTS : T ⊆ S) :
    inheritedSourceScale M P T = P S := by
  classical
  obtain ⟨S0, hS0, hunique⟩ := existsUnique_source_parent M hM Y hT
  have hS_eq := hunique S ⟨hS, hTS⟩
  have he : (sourceMaximalLadders M).filter (fun S' => T ⊆ S') = {S} := by
    ext S'
    simp only [mem_filter, mem_singleton]
    constructor
    · intro h
      exact (hunique S' h).trans hS_eq.symm
    · intro h
      subst S'
      exact ⟨hS, hTS⟩
  unfold inheritedSourceScale
  rw [he, sum_singleton]

/-- An unchanged old maximal ladder keeps its scale, without any choices. -/
theorem inheritedSourceScale_eq_on_old_maximal (M : Molecule V D) (P : Finset V → ℝ)
    {S : Finset V} (hS : S ∈ sourceMaximalLadders M) : inheritedSourceScale M P S = P S := by
  classical
  have hmax := (mem_filter.mp hS).2.2
  have he : (sourceMaximalLadders M).filter (fun S' => S ⊆ S') = {S} := by
    ext S'
    simp only [mem_filter, mem_singleton]
    constructor
    · intro h
      exact hmax S' (mem_filter.mp h.1).2.1 h.2
    · intro h
      subst S'
      exact ⟨hS, Subset.rfl⟩
  unfold inheritedSourceScale
  rw [he, sum_singleton]

/-- Erasure inherits the degree cap needed by the selected-ladder geometry. -/
theorem deg_eraseAtoms_le_four (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V) :
    ∀ z ∈ (eraseAtoms M Y).atoms, (eraseAtoms M Y).deg z ≤ 4 := by
  intro z hz
  obtain ⟨hzM, hzY⟩ := mem_sdiff.mp hz
  have hdeg := deg_eraseAtoms_add_removed M Y hzY
  have hcap := Mole.deg_le_four M hM hzM
  omega

end WaveTurbulence.Degen

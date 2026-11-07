/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold7
public import WaveTurbulence.Foundations.Vine.B.Shape
public import WaveTurbulence.Foundations.Vine.B.BranchSplit
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHinge
import Mathlib.Tactic

/-!
# VINE-B Part I (8): the `SpliceShape` of `G_sb = (stSt S σ).G`

For a molecule skeleton `S` and a prescription `σ`, the units `unitBlocks S σ` (indexed by `Fin length`) are pairwise
disjoint (`Disj`), and the fold invariant of `spliceFold` gives the `SpliceShape` of `(stSt S σ).G` with `br = M.ob`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

/-- The units of `σ` and the marked vine set `Mk`, indexed by position (B1a: the Mk-general family; main's
`unitBlk hM σ` is its value at `Mk = ∅`). -/
noncomputable abbrev unitBlkMk (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    Fin (unitBlocks S σ Mk).length → CLBlock S := fun j => (unitBlocks S σ Mk).get j

/-- The units of `σ`, indexed by position. -/
noncomputable abbrev unitBlk (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    Fin (unitBlocks S σ).length → CLBlock S := unitBlkMk hM σ ∅

/-- B1a: the units are disjoint for every marked vine set. -/
theorem unitBlkMk_disj (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    Disj (unitBlkMk hM σ Mk) := by
  intro j k hjk
  have hp := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk hM σ Mk)
  rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with h | h
  · exact hp j k h
  · exact (hp k j h).symm

theorem unitBlk_disj (hM : S.molecule.IsMolecule) (σ : Prescription S) : Disj (unitBlk hM σ) := by
  intro j k hjk
  have hp := List.pairwise_iff_get.mp (unitBlocks_pairwise hM σ)
  rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with h | h
  · exact hp j k h
  · exact (hp k j h).symm

/-- The fold invariant of `stSt S σ`. -/
noncomputable def stInv (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S) := ∅) :
    FoldInv (fun u => u ∈ unitBlocks S σ Mk) (stSt S σ Mk) :=
  spliceFoldInv S (unitBlocks S σ Mk) (unitBlocks_pairwiseMk hM σ Mk)

/-- **Part I.** The shape of the simultaneous splice `G_sb = (stSt S σ).G` inside the skeleton, with
`br = (stSt S σ).M.ob`. -/
noncomputable def stShape (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S) := ∅) :
    SpliceShape (unitBlkMk hM σ Mk) (stSt S σ Mk).G where
  node := (stInv hM σ Mk).node
  inj := (stInv hM σ Mk).inj
  range := fun x => ((stInv hM σ Mk).range x).trans
    ⟨fun h j => h _ (List.get_mem _ _), fun h u hu => by
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
      exact h j⟩
  tree_eq := (stInv hM σ Mk).tree_eq
  root := fun i => by
    apply Subtype.ext
    apply Prod.ext
    · exact (stInv hM σ Mk).tree_eq _
    · exact ((stInv hM σ Mk).root _).mpr rfl
  br := (stSt S σ Mk).M.ob
  br_node := (stInv hM σ Mk).br_node
  leaf := (stInv hM σ Mk).leaf
  leaf_node := (stInv hM σ Mk).leaf_node
  child := fun c i h => (stInv hM σ Mk).child c i (fun u hu => by
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
    exact h j)
  crown := fun c j h i => (stInv hM σ Mk).crown c _ (List.get_mem _ _) h i
  pair := (stInv hM σ Mk).pair
  sign := (stInv hM σ Mk).sign

theorem stShape_br (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    (stShape hM σ).br = (stSt S σ).M.ob := rfl

theorem stShape_hinges (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    (stShape hM σ).hinges (unitBlk_disj hM σ) = (stSt S σ).hinges := by
  ext c
  rw [(stShape hM σ).mem_hinges (unitBlk_disj hM σ), SpState.mem_hinges]
  constructor
  · rintro ⟨j, hj⟩
    rw [stShape_br] at hj
    rw [hj]
    rw [stSt_cls_mem hM σ (List.get_mem _ _) (upper_mem _)]
    simp
  · intro h
    -- the crown of the class of `ob c`
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
    by_cases hv : ∃ u ∈ unitBlocks S σ, (stSt S σ).M.ob c ∈ u.atoms
    · obtain ⟨u, hu, hvu⟩ := hv
      have hcl := stSt_cls_mem hM σ hu hvu
      have hr := (stSt S σ).M.ob_range ((stSt S σ).M.ob c)
      have : (stSt S σ).cls ((stSt S σ).M.ob c) = none ∨ (stSt S σ).cls ((stSt S σ).M.ob c) = some ((stSt S σ).M.ob c) :=
        hr.mp ⟨c, rfl⟩
      rcases this with h0 | h0
      · exact absurd h0 h
      · rw [hcl] at h0
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
        refine ⟨j, ?_⟩
        rw [stShape_br]
        exact (Option.some.inj h0).symm
    · exfalso
      push Not at hv
      exact h (stSt_cls_none hM σ hv)

/-- B1a: `stShape_hinges` for every marked vine set. -/
theorem stShape_hingesMk (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    (stShape hM σ Mk).hinges (unitBlkMk_disj hM σ Mk) = (stSt S σ Mk).hinges := by
  ext c
  rw [(stShape hM σ Mk).mem_hinges (unitBlkMk_disj hM σ Mk), SpState.mem_hinges]
  constructor
  · rintro ⟨j, hj⟩
    rw [show (stShape hM σ Mk).br = (stSt S σ Mk).M.ob from rfl] at hj
    rw [hj]
    rw [stSt_cls_memMk hM σ Mk (List.get_mem _ _) (upper_mem _)]
    simp
  · intro h
    -- the crown of the class of `ob c`
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
    by_cases hv : ∃ u ∈ unitBlocks S σ Mk, (stSt S σ Mk).M.ob c ∈ u.atoms
    · obtain ⟨u, hu, hvu⟩ := hv
      have hcl := stSt_cls_memMk hM σ Mk hu hvu
      have hr := (stSt S σ Mk).M.ob_range ((stSt S σ Mk).M.ob c)
      have : (stSt S σ Mk).cls ((stSt S σ Mk).M.ob c) = none ∨ (stSt S σ Mk).cls ((stSt S σ Mk).M.ob c) = some ((stSt S σ Mk).M.ob c) :=
        hr.mp ⟨c, rfl⟩
      rcases this with h0 | h0
      · exact absurd h0 h
      · rw [hcl] at h0
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
        refine ⟨j, ?_⟩
        rw [show (stShape hM σ Mk).br = (stSt S σ Mk).M.ob from rfl]
        exact (Option.some.inj h0).symm
    · exfalso
      push Not at hv
      exact h (stSt_cls_noneMk hM σ Mk hv)

end WaveTurbulence.VineB

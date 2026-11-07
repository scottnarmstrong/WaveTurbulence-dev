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

/-- The units of `σ`, indexed by position. -/
noncomputable abbrev unitBlk (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    Fin (unitBlocks S σ).length → CLBlock S := fun j => (unitBlocks S σ).get j

theorem unitBlk_disj (hM : S.molecule.IsMolecule) (σ : Prescription S) : Disj (unitBlk hM σ) := by
  intro j k hjk
  have hp := List.pairwise_iff_get.mp (unitBlocks_pairwise hM σ)
  rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with h | h
  · exact hp j k h
  · exact (hp k j h).symm

/-- The fold invariant of `stSt S σ`. -/
noncomputable def stInv (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    FoldInv (fun u => u ∈ unitBlocks S σ) (stSt S σ) :=
  spliceFoldInv S (unitBlocks S σ) (unitBlocks_pairwise hM σ)

/-- **Part I.** The shape of the simultaneous splice `G_sb = (stSt S σ).G` inside the skeleton, with
`br = (stSt S σ).M.ob`. -/
noncomputable def stShape (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    SpliceShape (unitBlk hM σ) (stSt S σ).G where
  node := (stInv hM σ).node
  inj := (stInv hM σ).inj
  range := fun x => ((stInv hM σ).range x).trans
    ⟨fun h j => h _ (List.get_mem _ _), fun h u hu => by
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
      exact h j⟩
  tree_eq := (stInv hM σ).tree_eq
  root := fun i => by
    apply Subtype.ext
    apply Prod.ext
    · exact (stInv hM σ).tree_eq _
    · exact ((stInv hM σ).root _).mpr rfl
  br := (stSt S σ).M.ob
  br_node := (stInv hM σ).br_node
  leaf := (stInv hM σ).leaf
  leaf_node := (stInv hM σ).leaf_node
  child := fun c i h => (stInv hM σ).child c i (fun u hu => by
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
    exact h j)
  crown := fun c j h i => (stInv hM σ).crown c _ (List.get_mem _ _) h i
  pair := (stInv hM σ).pair
  sign := (stInv hM σ).sign

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

end WaveTurbulence.VineB

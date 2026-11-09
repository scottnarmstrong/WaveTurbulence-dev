/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.B.Fold8` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.B.Fold7
public import WaveTurbulence.Foundations.Vine.B.Shape
public import WaveTurbulence.Foundations.Vine.B.BranchSplit
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHinge
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.B.Fold8
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects


/-!
# VINE-B Part I (8): the `SpliceShape` of `G_sb = (stSt γ S σ).G`

For a molecule skeleton `S` and a prescription `σ`, the units `unitBlocks γ S σ` (indexed by `Fin length`) are pairwise
disjoint (`Disj`), and the fold invariant of `spliceFold` gives the `SpliceShape` of `(stSt γ S σ).G` with `br = M.ob`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.VineB WaveTurbulence.GammaLow.FinalCount
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The units of `σ` and the marked vine set `Mk`, indexed by position (B1a: the Mk-general family; main's
`unitBlk γ hM σ` is its value at `Mk = ∅`). -/
noncomputable abbrev unitBlkMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    Fin (unitBlocks γ S σ Mk).length → CLBlock S := fun j => (unitBlocks γ S σ Mk).get j

/-- The units of `σ`, indexed by position. -/
noncomputable abbrev unitBlk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    Fin (unitBlocks γ S σ).length → CLBlock S := unitBlkMk γ hM σ ∅

/-- B1a: the units are disjoint for every marked vine set. -/
theorem unitBlkMk_disj (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    Disj (unitBlkMk γ hM σ Mk) := by
  intro j k hjk
  have hp := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk hM σ Mk)
  rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with h | h
  · exact hp j k h
  · exact (hp k j h).symm

theorem unitBlk_disj (hM : S.molecule.IsMolecule) (σ : Prescription S) : Disj (unitBlk γ hM σ) := by
  intro j k hjk
  have hp := List.pairwise_iff_get.mp (unitBlocks_pairwise (γ := γ) hM σ)
  rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with h | h
  · exact hp j k h
  · exact (hp k j h).symm

/-- The fold invariant of `stSt γ S σ`. -/
noncomputable def stInv (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S) := ∅) :
    FoldInv (fun u => u ∈ unitBlocks γ S σ Mk) (stSt γ S σ Mk) :=
  spliceFoldInv S (unitBlocks γ S σ Mk) (unitBlocks_pairwiseMk hM σ Mk)

/-- **Part I.** The shape of the simultaneous splice `G_sb = (stSt γ S σ).G` inside the skeleton, with
`br = (stSt γ S σ).M.ob`. -/
noncomputable def stShape (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S) := ∅) :
    SpliceShape (unitBlkMk γ hM σ Mk) (stSt γ S σ Mk).G where
  node := (stInv γ hM σ Mk).node
  inj := (stInv γ hM σ Mk).inj
  range := fun x => ((stInv γ hM σ Mk).range x).trans
    ⟨fun h j => h _ (List.get_mem _ _), fun h u hu => by
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
      exact h j⟩
  tree_eq := (stInv γ hM σ Mk).tree_eq
  root := fun i => by
    apply Subtype.ext
    apply Prod.ext
    · exact (stInv γ hM σ Mk).tree_eq _
    · exact ((stInv γ hM σ Mk).root _).mpr rfl
  br := (stSt γ S σ Mk).M.ob
  br_node := (stInv γ hM σ Mk).br_node
  leaf := (stInv γ hM σ Mk).leaf
  leaf_node := (stInv γ hM σ Mk).leaf_node
  child := fun c i h => (stInv γ hM σ Mk).child c i (fun u hu => by
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
    exact h j)
  crown := fun c j h i => (stInv γ hM σ Mk).crown c _ (List.get_mem _ _) h i
  pair := (stInv γ hM σ Mk).pair
  sign := (stInv γ hM σ Mk).sign

/-- B1b (Mk-general form of `stShape_br`). -/
theorem stShape_brMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ _)} :
    (stShape γ (Mk := Mk) hM σ).br = (stSt γ (Mk := Mk) S σ).M.ob := rfl

theorem stShape_br (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    (stShape γ hM σ).br = (stSt γ S σ).M.ob := stShape_brMk (Mk := ∅) hM σ

theorem stShape_hinges (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    (stShape γ hM σ).hinges (unitBlk_disj hM σ) = (stSt γ S σ).hinges := by
  ext c
  rw [(stShape γ hM σ).mem_hinges (unitBlk_disj hM σ), SpState.mem_hinges]
  constructor
  · rintro ⟨j, hj⟩
    rw [stShape_br] at hj
    rw [hj]
    rw [stSt_cls_mem (γ := γ) hM σ (List.get_mem _ _) (upper_mem _)]
    simp
  · intro h
    -- the crown of the class of `ob c`
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
    by_cases hv : ∃ u ∈ unitBlocks γ S σ, (stSt γ S σ).M.ob c ∈ u.atoms
    · obtain ⟨u, hu, hvu⟩ := hv
      have hcl := stSt_cls_mem (γ := γ) hM σ hu hvu
      have hr := (stSt γ S σ).M.ob_range ((stSt γ S σ).M.ob c)
      have : (stSt γ S σ).cls ((stSt γ S σ).M.ob c) = none ∨ (stSt γ S σ).cls ((stSt γ S σ).M.ob c) = some ((stSt γ S σ).M.ob c) :=
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
      exact h (stSt_cls_none (γ := γ) hM σ hv)

/-- B1a: `stShape_hinges` for every marked vine set. -/
theorem stShape_hingesMk (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    (stShape γ hM σ Mk).hinges (unitBlkMk_disj hM σ Mk) = (stSt γ S σ Mk).hinges := by
  ext c
  rw [(stShape γ hM σ Mk).mem_hinges (unitBlkMk_disj hM σ Mk), SpState.mem_hinges]
  constructor
  · rintro ⟨j, hj⟩
    rw [show (stShape γ hM σ Mk).br = (stSt γ S σ Mk).M.ob from rfl] at hj
    rw [hj]
    rw [stSt_cls_memMk hM σ Mk (List.get_mem _ _) (upper_mem _)]
    simp
  · intro h
    -- the crown of the class of `ob c`
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
    by_cases hv : ∃ u ∈ unitBlocks γ S σ Mk, (stSt γ S σ Mk).M.ob c ∈ u.atoms
    · obtain ⟨u, hu, hvu⟩ := hv
      have hcl := stSt_cls_memMk hM σ Mk hu hvu
      have hr := (stSt γ S σ Mk).M.ob_range ((stSt γ S σ Mk).M.ob c)
      have : (stSt γ S σ Mk).cls ((stSt γ S σ Mk).M.ob c) = none ∨ (stSt γ S σ Mk).cls ((stSt γ S σ Mk).M.ob c) = some ((stSt γ S σ Mk).M.ob c) :=
        hr.mp ⟨c, rfl⟩
      rcases this with h0 | h0
      · exact absurd h0 h
      · rw [hcl] at h0
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
        refine ⟨j, ?_⟩
        rw [show (stShape γ hM σ Mk).br = (stSt γ S σ Mk).M.ob from rfl]
        exact (Option.some.inj h0).symm
    · exfalso
      push Not at hv
      exact h (stSt_cls_noneMk hM σ Mk hv)

end WaveTurbulence.GammaLow.Fama

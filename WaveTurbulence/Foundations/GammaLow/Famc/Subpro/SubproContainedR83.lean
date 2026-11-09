/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.FinalCount.SubproIso3
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
-- R83 port of sp-src/SubproContained.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): TARGET `subpro` (4) (L2043--L2045), atom-set form

A vine-like object of `M_sb` that has no hinge atom and is not contained (by atoms) in an object of `C_1` is
contained (by atoms) in a DV or in an LG/ZG vine-like object, both disjoint from the hinges and from `C_1`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `mem_objects'`). -/
theorem mem_objects'Mk {σ : Prescription G} {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule} (h : O ∈ Fama.VineA.NormalizedSplice.objects γ (Mk := Mk) G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ Fama.VineA.NormalizedSplice.objOf γ (Mk := Mk) G σ S = some O := by
  unfold Fama.VineA.NormalizedSplice.objects at h
  obtain ⟨S, -, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, -, -⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Mk := Mk) hS
  exact ⟨S, h1, h2, hS⟩

theorem mem_objects' {σ : Prescription G} {O : Src.Object γ (stSt γ G σ).G.molecule} (h : O ∈ Fama.VineA.NormalizedSplice.objects γ G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ Fama.VineA.NormalizedSplice.objOf γ G σ S = some O := mem_objects'Mk (Mk := ∅) h

/-- B1b (Mk-general form of `objOf_none`). -/
theorem objOf_noneMk (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (h : ¬ (G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ Fama.VineA.NormalizedSplice.HasObj γ G S)) {Mk : Set (CLVineG γ _)} :
    Fama.VineA.NormalizedSplice.objOf γ (Mk := Mk) G σ S = none := by
  classical
  unfold Fama.VineA.NormalizedSplice.objOf
  rw [dif_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)]

theorem objOf_none (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (h : ¬ (G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ Fama.VineA.NormalizedSplice.HasObj γ G S)) :
    Fama.VineA.NormalizedSplice.objOf γ G σ S = none := objOf_noneMk (Mk := ∅) σ h

theorem objOf_some (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG) (hO : Fama.VineA.NormalizedSplice.HasObj γ G S) :
    ∃ O, Fama.VineA.NormalizedSplice.objOf γ G σ S = some O := by
  classical
  unfold Fama.VineA.NormalizedSplice.objOf
  rw [dif_pos ⟨hM, hS, hσ, hO, Fama.not_markedGroup_empty G S, Fama.VineA.NormalizedSplice.exists_obj hM σ hS hσ hO⟩]
  exact ⟨_, rfl⟩

theorem cover_group (hM : G.molecule.IsMolecule) {T : Finset (GBranch G.tree)} (hT : IsVineLikeSetG γ G.molecule T) :
    ∃ g ∈ maximalGroupsG γ G.molecule, T ⊆ g := by
  have hpart := maximalGroupsG_partition (γ := γ) hM
  obtain ⟨g, hg, hTg⟩ := Fama.cover_of_vineLike hpart hT
  exact ⟨g, by rw [← Fama.partition_eq_maximalGroups hpart]; exact hg, hTg⟩

/-- B1b (Mk-general form of `nohinge_unmerged`). -/
theorem nohinge_unmergedMk (σ : Prescription G) {Mk : Set (CLVineG γ _)} {P : Finset (GBranch (stSt γ (Mk := Mk) G σ).G.tree)}
    (hP : Disjoint P (stSt γ (Mk := Mk) G σ).hinges) : ∀ c ∈ P, (stSt γ (Mk := Mk) G σ).cls ((stSt γ (Mk := Mk) G σ).M.ob c) = none := by
  intro c hc
  by_contra h
  exact Finset.disjoint_left.mp hP hc (((stSt γ (Mk := Mk) G σ).mem_hinges c).mpr h)

theorem nohinge_unmerged (σ : Prescription G) {P : Finset (GBranch (stSt γ G σ).G.tree)}
    (hP : Disjoint P (stSt γ G σ).hinges) : ∀ c ∈ P, (stSt γ G σ).cls ((stSt γ G σ).M.ob c) = none := nohinge_unmergedMk (Mk := ∅) σ hP

/-- B1b (Mk-general form of `pi_ob`). -/
theorem pi_obMk (σ : Prescription G) {Mk : Set (CLVineG γ _)} {c : GBranch (stSt γ (Mk := Mk) G σ).G.tree} (h : (stSt γ (Mk := Mk) G σ).cls ((stSt γ (Mk := Mk) G σ).M.ob c) = none) :
    (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls ((stSt γ (Mk := Mk) G σ).M.ob c) = c := by
  apply (stSt γ (Mk := Mk) G σ).M.ob_inj
  rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, repC_of_none h]

theorem pi_ob (σ : Prescription G) {c : GBranch (stSt γ G σ).G.tree} (h : (stSt γ G σ).cls ((stSt γ G σ).M.ob c) = none) :
    (stSt γ G σ).M.pi (stSt γ G σ).hcls ((stSt γ G σ).M.ob c) = c := pi_obMk (Mk := ∅) σ h

/-- B1b (Mk-general form of `atoms_sub_obj`). -/
theorem atoms_sub_objMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule} (hO : Fama.VineA.NormalizedSplice.objOf γ (Mk := Mk) G σ S = some O) {P : Finset (GBranch (stSt γ (Mk := Mk) G σ).G.tree)}
    (hP : ∀ c ∈ P, (stSt γ (Mk := Mk) G σ).M.ob c ∈ S ∧ (stSt γ (Mk := Mk) G σ).cls ((stSt γ (Mk := Mk) G σ).M.ob c) = none) : P ⊆ O.atoms := by
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Mk := Mk) (Option.mem_def.mpr hO)
  obtain ⟨A, -, hOA, hnm, -⟩ := hSpec.src
  intro c hc
  obtain ⟨h1, h2⟩ := hP c hc
  rw [hOA]
  refine Finset.mem_image.mpr ⟨(stSt γ (Mk := Mk) G σ).M.ob c, hnm _ h1 h2, pi_obMk (Mk := Mk) σ h2⟩

/-- Atoms of `M_sb` that are unmerged images of atoms of an object's group lie in the object. -/
theorem atoms_sub_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    {O : Src.Object γ (stSt γ G σ).G.molecule} (hO : Fama.VineA.NormalizedSplice.objOf γ G σ S = some O) {P : Finset (GBranch (stSt γ G σ).G.tree)}
    (hP : ∀ c ∈ P, (stSt γ G σ).M.ob c ∈ S ∧ (stSt γ G σ).cls ((stSt γ G σ).M.ob c) = none) : P ⊆ O.atoms := atoms_sub_objMk (Mk := ∅) hM σ hO hP

theorem obj_group_of_mem (σ : Prescription G) {O : Src.Object γ (stSt γ G σ).G.molecule} (hO : O ∈ Fama.VineA.NormalizedSplice.objects γ G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ Fama.VineA.NormalizedSplice.objOf γ G σ S = some O :=
  mem_objects' hO


/-- B1b (Mk-general form of `mem_objects_of`). -/
theorem mem_objects_ofMk (σ : Prescription G) {S : Finset (GBranch G.tree)} {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule}
    (hS : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG) (hO : Fama.VineA.NormalizedSplice.objOf γ (Mk := Mk) G σ S = some O) :
    O ∈ Fama.VineA.NormalizedSplice.objects γ (Mk := Mk) G σ := by
  unfold Fama.VineA.NormalizedSplice.objects
  exact List.mem_filterMap.mpr ⟨S, Fama.mem_sgGroups.mpr ⟨hS, hσ⟩, hO⟩

theorem mem_objects_of (σ : Prescription G) {S : Finset (GBranch G.tree)} {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hS : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG) (hO : Fama.VineA.NormalizedSplice.objOf γ G σ S = some O) :
    O ∈ Fama.VineA.NormalizedSplice.objects γ G σ := mem_objects_ofMk (Mk := ∅) σ hS hσ hO

theorem containsDart_inGroup {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (O : Src.Object γ M) {x : D} (h : O.ContainsDart x) : M.InGroup O.atoms x := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc _ => exact h
  | hyper _ => exact h.2.2

/-- B1b (Mk-general form of `image_pi_disjoint_hinges`). -/
theorem image_pi_disjoint_hingesMk (σ : Prescription G) {g : Finset (GBranch G.tree)}
    {Mk : Set (CLVineG γ _)} (hall : ∀ z0 ∈ g, (stSt γ (Mk := Mk) G σ).cls z0 = none) :
    Disjoint (g.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls)) (stSt γ (Mk := Mk) G σ).hinges := by
  rw [Finset.disjoint_left]
  intro v hv hh
  obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hv
  have := ((stSt γ (Mk := Mk) G σ).mem_hinges _).mp hh
  rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, repC_of_none (hall z0 hz0)] at this
  exact this (hall z0 hz0)

/-- The images of the unmerged atoms of a group are disjoint from the hinges. -/
theorem image_pi_disjoint_hinges (σ : Prescription G) {g : Finset (GBranch G.tree)}
    (hall : ∀ z0 ∈ g, (stSt γ G σ).cls z0 = none) :
    Disjoint (g.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls)) (stSt γ G σ).hinges := image_pi_disjoint_hingesMk (Mk := ∅) σ hall

/-- B1b (Mk-general form of `image_pi_disjoint_objects`). -/
theorem image_pi_disjoint_objectsMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {g : Finset (GBranch G.tree)}
    (hg : g ∈ maximalGroupsG γ G.molecule) {Mk : Set (CLVineG γ _)} (hall : ∀ z0 ∈ g, (stSt γ (Mk := Mk) G σ).cls z0 = none)
    (hO : Fama.VineA.NormalizedSplice.objOf γ (Mk := Mk) G σ g = none) :
    ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ (Mk := Mk) G σ, Disjoint (g.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls)) O.atoms := by
  intro O hOm
  obtain ⟨S1, -, hS1, hO1⟩ := mem_objects'Mk (Mk := Mk) hOm
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Mk := Mk) (Option.mem_def.mpr hO1)
  rw [Finset.disjoint_left]
  intro v hv hvO
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z2, hz2, hz12⟩ := hSpec.atoms_sub _ hvO
  have e : repC (stSt γ (Mk := Mk) G σ).cls z1 = repC (stSt γ (Mk := Mk) G σ).cls z2 := by
    rw [← (stSt γ (Mk := Mk) G σ).M.ob_pi (stSt γ (Mk := Mk) G σ).hcls z1, ← (stSt γ (Mk := Mk) G σ).M.ob_pi (stSt γ (Mk := Mk) G σ).hcls z2, hz12]
  have h1 : repC (stSt γ (Mk := Mk) G σ).cls z1 ∈ g := by rw [repC_of_none (hall z1 hz1)]; exact hz1
  have h2 : repC (stSt γ (Mk := Mk) G σ).cls z2 ∈ S1 := Fama.VineA.NormalizedSplice.repC_mem_groupMk (Mk := Mk) hM σ hS1 hz2
  have hgS : g = S1 := by
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hg hS1 hne) h1 (e ▸ h2)
  rw [hgS] at hO
  rw [hO] at hO1
  cases hO1

/-- The image of a group without an object of `C_1` is disjoint from the Fama.VineA.NormalizedSplice.objects γ of `C_1`. -/
theorem image_pi_disjoint_objects (hM : G.molecule.IsMolecule) (σ : Prescription G) {g : Finset (GBranch G.tree)}
    (hg : g ∈ maximalGroupsG γ G.molecule) (hall : ∀ z0 ∈ g, (stSt γ G σ).cls z0 = none)
    (hO : Fama.VineA.NormalizedSplice.objOf γ G σ g = none) :
    ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, Disjoint (g.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls)) O.atoms := image_pi_disjoint_objectsMk (Mk := ∅) hM σ hg hall hO

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro

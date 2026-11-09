/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport


/-!
# R83 successor copy (source pinned/r83-RedSpliceColl2.lean; SHA in COPIED-SHA256SUMS).
# REDSPLICE-DEF (S2a), B: `Src.SubproChoices γ` of `G_sb`

`objects γ G σ`: the objects γ of `C_1`; `ProperPair`.  (R28: `hingePair`, `collectionChoices` and their theorems moved
to `RedSpliceHingePair`, after the designated pairs of `RedSpliceDesig`.)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The object of the SG group `S` in `G_sb` (if it contributes one). -/
@[expose] noncomputable def objOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVineG γ G) := ∅) : Option (Src.Object γ (stSt γ G σ Mk).G.molecule) := by
  classical
  exact if h : G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj γ G S ∧
      ¬ markedGroup γ G Mk S ∧ ∃ O : Src.Object γ (stSt γ G σ Mk).G.molecule, ObjSpecMk γ G σ S Mk O then
    some (Classical.choose h.2.2.2.2.2) else none

/-- The objects γ of `C_1`.  B1a: with the marked vine set `Mk` (default `∅`), the objects γ of the unmarked SG groups
(o75: `𝒞₁` = main's objects γ restricted to `¬ markedGroup`). -/
@[expose] noncomputable def objects (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) :
    List (Src.Object γ (stSt γ G σ Mk).G.molecule) :=
  (sgGroups γ G σ).filterMap (fun S => objOf γ G σ S Mk)

/-- B1b (Mk-general form of `objOf_spec`). -/
theorem objOf_specMk {σ : Prescription G} {S : Finset (GBranch G.tree)} {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule}
    (h : O ∈ objOf γ (Mk := Mk) G σ S) :
    G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpecMk γ (Mk := Mk) G σ S O := by
  classical
  unfold objOf at h
  split_ifs at h with hh
  · rw [Option.mem_def, Option.some.injEq] at h
    subst h
    exact ⟨hh.1, hh.2.1, hh.2.2.1, Classical.choose_spec hh.2.2.2.2.2⟩
  · simp at h

theorem objOf_spec {σ : Prescription G} {S : Finset (GBranch G.tree)} {O : Src.Object γ (stSt γ G σ).G.molecule}
    (h : O ∈ objOf γ G σ S) :
    G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpec γ G σ S O := objOf_specMk (Mk := ∅) h

/-- B1b (Mk-general form of `mem_objects`). -/
theorem mem_objectsMk {σ : Prescription G} {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule} (h : O ∈ objects γ (Mk := Mk) G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpecMk γ (Mk := Mk) G σ S O := by
  unfold objects at h
  obtain ⟨S, _, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, h3, h4⟩ := objOf_specMk (Mk := Mk) hS
  exact ⟨S, h1, h2, h3, h4⟩


/-- B1b (Mk-general form of `objects_pairwise`). -/
theorem objects_pairwiseMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVineG γ _)} :
    (objects γ (Mk := Mk) G σ).Pairwise (fun O O' => Disjoint O.atoms O'.atoms) := by
  classical
  unfold objects
  rw [List.pairwise_filterMap]
  have hnd : (sgGroups γ G σ).Nodup := (Finset.nodup_toList _).filter _
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro S T hS hT hne O hO O' hO'
  obtain ⟨_, hSm, _, hSpec⟩ := objOf_specMk (Mk := Mk) hO
  obtain ⟨_, hTm, _, hTpec⟩ := objOf_specMk (Mk := Mk) hO'
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨z, hz, rfl⟩ := hSpec.atoms_sub v hv
  obtain ⟨z', hz', hzz⟩ := hTpec.atoms_sub _ hv'
  have h1 := (stSt γ (Mk := Mk) G σ).M.ob_pi (stSt γ (Mk := Mk) G σ).hcls z
  have h2 := (stSt γ (Mk := Mk) G σ).M.ob_pi (stSt γ (Mk := Mk) G σ).hcls z'
  rw [← hzz] at h2
  have e : repC (stSt γ (Mk := Mk) G σ).cls z = repC (stSt γ (Mk := Mk) G σ).cls z' := h1.symm.trans h2
  exact Finset.disjoint_left.mp (groups_disjoint hM hSm hTm hne) (repC_mem_groupMk (Mk := Mk) hM σ hSm hz)
    (e ▸ repC_mem_groupMk (Mk := Mk) hM σ hTm hz')


/-- A **proper hinge pair** at the hinge `v` is the lift of an external out/in pair of a unit (the unit whose crown
is `v`) at one of its joints (TARGET `subpro` (5): "the two bonds at one joint of `U` that do not belong to `U`"). -/
@[expose] def ProperPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree)
    (x y : GardenDart (stSt γ G σ Mk).G) : Prop :=
  TripleAt (stSt γ G σ Mk).G v x y ∧ ∃ u ∈ unitBlocks γ G σ Mk, (stSt γ G σ Mk).M.ob v = u.upper ∧
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ G σ Mk).M.od x) = j ∧
      G.molecule.atom ((stSt γ G σ Mk).M.od y) = j ∧
      ¬ G.molecule.InGroup u.atoms ((stSt γ G σ Mk).M.od x) ∧ ¬ G.molecule.InGroup u.atoms ((stSt γ G σ Mk).M.od y)

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice

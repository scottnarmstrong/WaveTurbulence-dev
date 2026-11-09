/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitClasses` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.RepPr2Supp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineCoarseGroupCodeSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineBatchSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineFamilySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineOperationSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRebaseSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRecoverySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRefinementSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizedRepSelSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescriptionSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrimeStateSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineUnitCoverSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.Vine.A.VineSpliceOrder
public import WaveTurbulence.Foundations.Vine.A.VineUnitClasses
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
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
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Actual selected unit transport intertwines the complete merge classes.
The active lower node and every active internal dart are merged away. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `unitBlocks_cls_twist`, two marked sets carried by the twist). -/
theorem unitBlocks_cls_twistMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (v : GBranch G.tree) :
    (spliceFold Z.target (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).cls (Z.iso.e v) =
      ((spliceFold G (unitBlocks γ G σ Mk)).cls v).map Z.iso.e := by
  classical
  have hs := unitBlocks_pairwiseMk (Mole.garden_isMolecule G) σ Mk
  have ht := unitBlocks_pairwiseMk (Mole.garden_isMolecule Z.target) (transportPrescription Z.iso σ) Mk'
  by_cases hv : ∃ u ∈ unitBlocks γ G σ Mk, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := hv
    have hmu := unitImage_memMk Z σ hT hsel hu
    have hmv : Z.iso.e v ∈ (Famc.VineA.unitImage γ Z u (Famc.VineA.unitBlocks_goodMk Z σ hsel hu)).atoms :=
      (Z.iso.mem_img u.atoms v).mpr hv
    rw [spliceFold_cls_mem _ hs hu hv, spliceFold_cls_mem _ ht hmu hmv]
    rfl
  · have hn : ∀ u ∈ unitBlocks γ G σ Mk, v ∉ u.atoms := fun u hu h => hv ⟨u, hu, h⟩
    have hn' : ∀ u' ∈ unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk', Z.iso.e v ∉ u'.atoms := by
      intro u' hu' hm
      obtain ⟨u, hu, hat, _, _⟩ := unitBlocks_preimageMk Z σ hT hsel hu'
      rw [hat] at hm
      exact hn u hu ((Z.iso.mem_img u.atoms v).mp hm)
    rw [spliceFold_cls_notMem _ hs hn, spliceFold_cls_notMem _ ht hn']
    rfl


/-- B1b-2 (Mk-general form of `unitBlocks_repC_twist`). -/
theorem unitBlocks_repC_twistMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (v : GBranch G.tree) :
    repC (spliceFold Z.target (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).cls (Z.iso.e v) =
      Z.iso.e (repC (spliceFold G (unitBlocks γ G σ Mk)).cls v) := by
  unfold repC
  rw [unitBlocks_cls_twistMk Z σ hT hsel v]
  cases (spliceFold G (unitBlocks γ G σ Mk)).cls v <;> rfl


/-- B1b (Mk-general form of `active_support_unit`). -/
theorem active_support_unitMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ _)} (hsel : ∃ c ∈ vinesV0 γ (Mk := Mk) G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, Z.S0 ⊆ u.atoms := by
  obtain ⟨c, hc, hat⟩ := hsel
  obtain ⟨_, u, hu, hsub⟩ := (vinesV0_iff_unit_cover_diffMk (Mk := Mk) G σ c).mp hc
  exact ⟨u, hu, hat ▸ hsub⟩


/-- B1b (Mk-general form of `active_lower_merged`). -/
theorem active_lower_mergedMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ _)} (hsel : ∃ c ∈ vinesV0 γ (Mk := Mk) G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, (spliceFold G (unitBlocks γ (Mk := Mk) G σ)).cls Z.P.lower = some u.upper ∧ u.upper ≠ Z.P.lower := by
  obtain ⟨u, hu, hsub⟩ := active_support_unitMk (Mk := Mk) Z σ hsel
  have hp := internalParent_mono hsub Z.hCL.2
  refine ⟨u, hu, spliceFold_cls_mem _ (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu
    (hsub Z.hB.2.2.1), ?_⟩
  intro he
  exact u.cl.1 (he.symm ▸ hp)


/-- B1b (Mk-general form of `active_internal_dart_merged`). -/
theorem active_internal_dart_mergedMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ _)} (hsel : ∃ c ∈ vinesV0 γ (Mk := Mk) G σ, c.atoms = Z.S0) {d : GardenDart G}
    (hd : G.molecule.InGroup Z.S0 d) :
    ∃ a, (spliceFold G (unitBlocks γ (Mk := Mk) G σ)).cls (G.molecule.atom d) = some a ∧
      (spliceFold G (unitBlocks γ (Mk := Mk) G σ)).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
  obtain ⟨u, hu, hsub⟩ := active_support_unitMk (Mk := Mk) Z σ hsel
  have hmem : ∀ {v}, v ∈ u.atoms → (spliceFold G (unitBlocks γ (Mk := Mk) G σ)).cls v = some u.upper :=
    fun hv => spliceFold_cls_mem (unitBlocks γ (Mk := Mk) G σ) (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu hv
  exact ⟨u.upper, hmem (hsub hd.1), hmem (hsub hd.2)⟩


end WaveTurbulence.GammaLow.Fama.VineA

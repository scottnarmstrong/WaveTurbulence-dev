/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDarts` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDarts
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitDeletedDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceBranch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceChildren
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! The actual selected-splice dart map preserves PC/LP tags and agrees
with the full node map on the exact bond-momentum arguments of the kernel. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
variable {w d : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `unitSpliceLP_profile_iff`). -/
theorem unitSpliceLP_profile_iffMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    ((stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.mark (unitSpliceLeafEquivMk γ Z σ hT hsel q) = none ∧
      (unitSpliceLeafEquivMk γ Z σ hT hsel q).1.2 ≠ [] ∧
      ((stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.pair (unitSpliceLeafEquivMk γ Z σ hT hsel q)).1.2 ≠ []) ↔
    ((stSt γ G σ Mk).G.mark q = none ∧ q.1.2 ≠ [] ∧ ((stSt γ G σ Mk).G.pair q).1.2 ≠ []) := by
  have hm := Iff.of_eq (congrArg (fun x : Option MarkTag => x = none) (unitSpliceLeafEquiv_markMk Z σ hT hsel q))
  have hr := not_congr (unitSpliceLeafEquiv_rootMk Z σ hT hsel q)
  have hp := (Iff.of_eq (congrArg (fun l : GLeaf (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree => l.1.2 ≠ [])
    (unitSpliceLeafEquiv_pairMk Z σ hT hsel q).symm)).trans
      (not_congr (unitSpliceLeafEquiv_rootMk Z σ hT hsel ((stSt γ G σ Mk).G.pair q)))
  exact and_congr hm (and_congr hr hp)


/-- B1b-2 (Mk-general form of `unitSpliceLPLeafEquiv`). -/
noncomputable def unitSpliceLPLeafEquivMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    GardenLPLeaf (stSt γ G σ Mk).G ≃ GardenLPLeaf (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G :=
  (unitSpliceLeafEquivMk γ Z σ hT hsel).subtypeEquiv (fun q => (unitSpliceLP_profile_iffMk Z σ hT hsel q).symm)


/-- B1b-2 (Mk-general form of `unitSplicePCEquiv`). -/
noncomputable def unitSplicePCEquivMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    {c : GBranch (stSt γ G σ Mk).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree // c.1.2 ≠ []} :=
  (unitSpliceMolIsoMk γ Z σ hT hsel).e.subtypeEquiv
    (fun c => (not_congr (unitSpliceMolIso_branch_rootMk Z σ hT hsel c)).symm)


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_pc`). -/
theorem unitSpliceMolIso_pcMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (c : {c : GBranch (stSt γ G σ Mk).G.tree // c.1.2 ≠ []}) (side : Bool) :
    (unitSpliceMolIsoMk γ Z σ hT hsel).d (.inl (c, side)) = .inl (unitSplicePCEquivMk γ Z σ hT hsel c, side) := by
  apply (stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.od_inj
  have he : naiveDartEquiv G Z.P (.inl (spliceOldPC (stSt γ G σ Mk) c, side)) =
      .inl (spliceOldPC (stSt γ Z.target (transportPrescription Z.iso σ) Mk') (unitSplicePCEquivMk γ Z σ hT hsel c), side) := by
    apply congrArg (fun b => Sum.inl (b, side))
    apply Subtype.ext
    exact (unitSpliceMolIso_branch_namesMk Z σ hT hsel c.1).symm
  exact (unitSpliceMolIso_surviving_dart_namesMk Z σ hT hsel (.inl (c, side))).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks γ G σ Mk)).pc c side)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).pc _ side).symm))


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_lp`). -/
theorem unitSpliceMolIso_lpMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GardenLPLeaf (stSt γ G σ Mk).G) :
    (unitSpliceMolIsoMk γ Z σ hT hsel).d (.inr q) = .inr (unitSpliceLPLeafEquivMk γ Z σ hT hsel q) := by
  apply (stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.od_inj
  have he : naiveDartEquiv G Z.P (.inr ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).lp q)) =
      .inr ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).lp
        (unitSpliceLPLeafEquivMk γ Z σ hT hsel q)) := by
    apply congrArg Sum.inr
    apply Subtype.ext
    exact (unitSpliceLeafEquiv_namesMk Z σ hT hsel q.1).symm
  exact (unitSpliceMolIso_surviving_dart_namesMk Z σ hT hsel (.inr q)).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks γ G σ Mk)).lp q)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).lp _).symm))


/-- B1b-2 (Mk-general form of `unitSplice_bondIndex`). -/
theorem unitSplice_bondIndexMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (z : GNode (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree → (Fin d → ℤ))
    (x : GardenDart (stSt γ G σ Mk).G) :
    bondIndex (stSt γ G σ Mk).G (z ∘ unitSpliceNodeEquivMk γ Z σ hT hsel) x =
      bondIndex (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G z ((unitSpliceMolIsoMk γ Z σ hT hsel).d x) := by
  cases x with
  | inl c =>
    obtain ⟨c, side⟩ := c
    rw [unitSpliceMolIso_pcMk]
    exact congrArg z (unitSpliceNodeEquiv_branchMk Z σ hT hsel c.1)
  | inr q =>
    rw [unitSpliceMolIso_lpMk]
    exact congrArg z (unitSpliceNodeEquiv_leafMk Z σ hT hsel q.1)


end WaveTurbulence.GammaLow.Fama.VineA

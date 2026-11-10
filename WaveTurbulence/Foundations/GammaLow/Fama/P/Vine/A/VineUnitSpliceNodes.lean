/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceNodes` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceTimeDomain
public import WaveTurbulence.Foundations.Molecule.TwistNodeLabels
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! The complete actual node correspondence of selected simultaneous
splices, with signed rooted-forest and parent compatibility. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv`). -/
noncomputable def unitSpliceNodeEquivMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    GNode (stSt γ G σ Mk).G.tree ≃ GNode (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree :=
  (nodePieceEquiv (stSt γ G σ Mk).G.tree).symm.trans
    ((Equiv.sumCongr (unitSpliceMolIsoMk γ Z σ hT hsel).e (unitSpliceLeafEquivMk γ Z σ hT hsel)).trans
      (nodePieceEquiv (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree))


/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_branch`). -/
theorem unitSpliceNodeEquiv_branchMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt γ G σ Mk).G.tree) :
    unitSpliceNodeEquivMk γ Z σ hT hsel b.toNode = ((unitSpliceMolIsoMk γ Z σ hT hsel).e b).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inl b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl


/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_leaf`). -/
theorem unitSpliceNodeEquiv_leafMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    unitSpliceNodeEquivMk γ Z σ hT hsel q.toNode = (unitSpliceLeafEquivMk γ Z σ hT hsel q).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inr q)))) = _
  rw [Equiv.symm_apply_apply]
  rfl


/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_sign`). -/
theorem unitSpliceNodeEquiv_signMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (n : GNode (stSt γ G σ Mk).G.tree) :
    (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.sign (unitSpliceNodeEquivMk γ Z σ hT hsel n) =
      (stSt γ G σ Mk).G.sign n := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt γ G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg _ (unitSpliceNodeEquiv_branchMk Z σ hT hsel b)).trans (unitSpliceMolIso_branch_signMk Z σ hT hsel b)
  | inr q => exact (congrArg _ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans (unitSpliceLeafEquiv_signMk Z σ hT hsel q)


/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_index`). -/
theorem unitSpliceNodeEquiv_indexMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (n : GNode (stSt γ G σ Mk).G.tree) :
    (unitSpliceNodeEquivMk γ Z σ hT hsel n).1.1 = n.1.1 := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt γ G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_branchMk Z σ hT hsel b)).trans (unitSpliceMolIso_branch_indexMk Z σ hT hsel b)
  | inr q => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans (unitSpliceLeafEquiv_indexMk Z σ hT hsel q)


/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_root`). -/
theorem unitSpliceNodeEquiv_rootMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (n : GNode (stSt γ G σ Mk).G.tree) :
    (unitSpliceNodeEquivMk γ Z σ hT hsel n).1.2 = [] ↔ n.1.2 = [] := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt γ G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_branchMk Z σ hT hsel b))).trans (unitSpliceMolIso_branch_rootMk Z σ hT hsel b)
  | inr q => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q))).trans (unitSpliceLeafEquiv_rootMk Z σ hT hsel q)



/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_parent`). -/
theorem unitSpliceNodeEquiv_parentMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (n : GNode (stSt γ G σ Mk).G.tree) (hn : n.1.2 ≠ []) :
    let e := unitSpliceNodeEquivMk γ Z σ hT hsel
    let hnew : (e n).1.2 ≠ [] := fun h => hn ((unitSpliceNodeEquiv_rootMk Z σ hT hsel n).mp h)
    (unitSpliceMolIsoMk γ Z σ hT hsel).e (GNode.parent n hn) = GNode.parent (e n) hnew := by
  dsimp only
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt γ G σ Mk).G.tree).surjective n
  cases x with
  | inl b =>
    have hb : ((unitSpliceMolIsoMk γ Z σ hT hsel).e b).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel b).mp h)
    exact (unitSpliceMolIso_parentMk Z σ hT hsel b hn).trans
      (spliceNodeParent_congr hb _ (unitSpliceNodeEquiv_branchMk Z σ hT hsel b).symm)
  | inr q =>
    have hq : (unitSpliceLeafEquivMk γ Z σ hT hsel q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
    exact (unitSpliceLeafEquiv_parentMk Z σ hT hsel q hn).trans
      (spliceNodeParent_congr hq _ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q).symm)


end WaveTurbulence.GammaLow.Fama.VineA

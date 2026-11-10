/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceBranch` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.Vine.A.VineSpliceBranchTrace
public import WaveTurbulence.Foundations.Molecule.TwistParents
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceBranch
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Actual selected unit LF twists preserve the signs, roots and parent
relations of branches surviving the actual simultaneous splice. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_sign`). -/
theorem unitSpliceMolIso_branch_signMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (c : GBranch (stSt γ G σ Mk).G.tree) :
    (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.sign
      ((unitSpliceMolIsoMk γ Z σ hT hsel).e c).toNode = (stSt γ G σ Mk).G.sign c.toNode := by
  have hn : (stSt γ G σ Mk).M.ob c ≠ Z.P.lower :=
    fun he => active_lower_not_survivingMk Z σ hsel ⟨c, he⟩
  calc
    _ = Z.target.sign ((stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.ob
        ((unitSpliceMolIsoMk γ Z σ hT hsel).e c)).toNode :=
      (spliceFoldBranchTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).sign _
    _ = Z.target.sign (Z.iso.e ((stSt γ G σ Mk).M.ob c)).toNode :=
      congrArg (fun b : GBranch Z.target.tree => Z.target.sign b.toNode) (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)
    _ = G.sign ((stSt γ G σ Mk).M.ob c).toNode :=
      (coreBranchEquiv_sign G Z.P _).trans (ite_eq_right hn)
    _ = _ := ((spliceFoldBranchTrace (unitBlocks γ G σ Mk)).sign c).symm


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_root`). -/
theorem unitSpliceMolIso_branch_rootMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (c : GBranch (stSt γ G σ Mk).G.tree) :
    ((unitSpliceMolIsoMk γ Z σ hT hsel).e c).1.2 = [] ↔ c.1.2 = [] := by
  exact ((stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.ob_root _).symm.trans
    ((Iff.of_eq (congrArg (fun b : GBranch Z.target.tree => b.1.2 = [])
      (unitSpliceMolIso_branch_namesMk Z σ hT hsel c))).trans
        ((coreBranch_root_iff Z.P _).trans ((stSt γ G σ Mk).M.ob_root c)))


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_root_address`). -/
theorem unitSpliceMolIso_root_addressMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt γ G σ Mk).G.tree)
    (hroot : c.1.2 = []) : ((unitSpliceMolIsoMk γ Z σ hT hsel).e c).1 = c.1 := by
  have hm := (unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mpr hroot
  have hold := ((stSt γ G σ Mk).M.ob_root c).mpr hroot
  exact ((spliceFoldBranchTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).root_address _ hm).symm.trans
    ((congrArg Subtype.val (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)).trans
      ((coreBranch_root_address Z.P _ hold).trans
        ((spliceFoldBranchTrace (unitBlocks γ G σ Mk)).root_address c hroot)))


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_parent`). -/
theorem unitSpliceMolIso_parentMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt γ G σ Mk).G.tree) (hn : c.1.2 ≠ []) :
    let F := unitSpliceMolIsoMk γ Z σ hT hsel
    let hnew : (F.e c).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mp h)
    F.e (GNode.parent c.toNode hn) = GNode.parent (F.e c).toNode hnew := by
  dsimp only
  let F := unitSpliceMolIsoMk γ Z σ hT hsel
  let M := (stSt γ G σ Mk).M
  let N := (stSt γ Z.target (transportPrescription Z.iso σ) Mk').M
  have hnew : (F.e c).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mp h)
  have ho : (M.ob c).1.2 ≠ [] := fun h => hn ((M.ob_root c).mp h)
  have hon : (N.ob (F.e c)).1.2 ≠ [] := fun h => hnew ((N.ob_root (F.e c)).mp h)
  have hne : M.ob c ≠ Z.P.lower := fun he => active_lower_not_survivingMk Z σ hsel ⟨c, he⟩
  have hpn : GNode.parent (N.ob (F.e c)).toNode hon =
      GNode.parent (Z.iso.e (M.ob c)).toNode ((coreBranchEquiv_nonroot G Z.P _).mpr ho) := by
    apply Subtype.ext
    change ((N.ob (F.e c)).1.1, (N.ob (F.e c)).1.2.dropLast) =
      ((Z.iso.e (M.ob c)).1.1, (Z.iso.e (M.ob c)).1.2.dropLast)
    exact congrArg (fun b : GBranch Z.target.tree => (b.1.1, b.1.2.dropLast))
      (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)
  have hp : GNode.parent (N.ob (F.e c)).toNode hon = Z.iso.e (GNode.parent (M.ob c).toNode ho) :=
    hpn.trans (branchParent_transport G Z.P (M.ob c) ho hne)
  apply N.ob_inj
  rw [unitSpliceMolIso_branch_namesMk, M.ob_parent c hn ho, N.ob_parent (F.e c) hnew hon,
    hp]
  exact (unitBlocks_repC_twistMk Z σ hT hsel (GNode.parent (M.ob c).toNode ho)).symm


/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_index`). -/
theorem unitSpliceMolIso_branch_indexMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt γ G σ Mk).G.tree) :
    ((unitSpliceMolIsoMk γ Z σ hT hsel).e c).1.1 = c.1.1 := by
  by_cases hroot : c.1.2 = []
  · exact congrArg Prod.fst (unitSpliceMolIso_root_addressMk Z σ hT hsel c hroot)
  · have hp := unitSpliceMolIso_parentMk Z σ hT hsel c hroot
    have hi := unitSpliceMolIso_branch_indexMk Z σ hT hsel (GNode.parent c.toNode hroot)
    have he := congrArg (fun b : GBranch (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree => b.1.1) hp
    exact he.symm.trans hi
termination_by c.1.2.length
decreasing_by
  change c.1.2.dropLast.length < c.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hroot
  omega


end WaveTurbulence.GammaLow.Fama.VineA

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceOuter` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.Vine.A.VineSpliceChildRange
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceChildren
public import WaveTurbulence.Foundations.Vine.A.VinePortRigidity
public import WaveTurbulence.Foundations.Molecule.CoreBranchAddresses
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceOuter
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! An outer slot is fixed by the actual selected LF quotient map. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `unitSplice_old_child`). -/
theorem unitSplice_old_childMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt γ G σ Mk).G.tree) (n : GNode (stSt γ G σ Mk).G.tree) (i : Fin 3)
    (hc : spliceOldNode (unitBlocks γ G σ Mk) n = ((stSt γ G σ Mk).M.ob b).child i) :
    spliceOldNode (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')
      (unitSpliceNodeEquivMk γ Z σ hT hsel n) =
      ((stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.ob ((unitSpliceMolIsoMk γ Z σ hT hsel).e b)).child i := by
  have hb : (stSt γ G σ Mk).M.ob b ≠ Z.P.lower :=
    fun h => active_lower_not_survivingMk Z σ hsel ⟨b, h⟩
  have hslot : exchangeChildSlot Z.P.lower.1 Z.P.keep ((stSt γ G σ Mk).M.ob b).1 i = i := by
    unfold exchangeChildSlot
    exact ite_eq_right (fun h => hb (Subtype.ext h))
  rw [unitSpliceMolIso_branch_namesMk]
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (stSt γ G σ Mk).G.tree).surjective n
  cases p with
  | inl c =>
    have hc' := (spliceOldNode_branch (unitBlocks γ G σ Mk) c).symm.trans hc
    have he := branch_child_transport G Z.P hc'
      (fun h => active_lower_not_survivingMk Z σ hsel ⟨c, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_branchMk Z σ hT hsel c)).trans
      ((spliceOldNode_branch _ _).trans
        ((congrArg GBranch.toNode (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)).trans he))
  | inr q =>
    have hc' := (spliceOldNode_leaf (unitBlocks γ G σ Mk) q).symm.trans hc
    have he := leaf_child_transport G Z.P hc'
      (fun h => active_pair_not_survivingMk Z σ hsel ⟨q, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans
      ((spliceOldNode_leaf _ _).trans
        ((congrArg GLeaf.toNode (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans he))


/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_of_external`). -/
theorem unitSpliceChildSlot_of_externalMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt γ G σ Mk).G.tree) (i : Fin 3)
    (hext : ∀ u ∈ unitBlocks γ G σ Mk, i.succ ∉ internalPositions G u.atoms ((stSt γ G σ Mk).M.ob b)) :
    unitSpliceChildSlotMk γ Z σ hT hsel b i = i := by
  let l := unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk'
  let n := unitSpliceNodeEquivMk γ Z σ hT hsel (b.child i)
  let v := (stSt γ Z.target (transportPrescription Z.iso σ) Mk').M.ob ((unitSpliceMolIsoMk γ Z σ hT hsel).e b)
  have he : spliceOldNode l n = v.child i := unitSplice_old_childMk Z σ hT hsel b (b.child i) i
    (spliceOldNode_child_external _ (unitBlocks_pairwiseMk (garden_isMolecule G) σ Mk) b i hext)
  have hn : n.1.2 ≠ [] := fun h => child_nonroot (stSt γ G σ Mk).G b i
    ((unitSpliceNodeEquiv_rootMk Z σ hT hsel (b.child i)).mp h)
  have ho : (spliceOldNode l n).1.2 ≠ [] := fun h => child_nonroot Z.target v i
    ((congrArg (fun n : GNode Z.target.tree => n.1.2) he).symm.trans h)
  have hp : GNode.parent (spliceOldNode l n) ho = v :=
    (spliceNodeParent_congr ho (child_nonroot Z.target v i) he).trans (parent_child_branch_eq Z.target v i _)
  have hf : repC (spliceFold Z.target l).cls (GNode.parent (spliceOldNode l n) ho) =
      GNode.parent (spliceOldNode l n) ho := by
    rw [hp]
    exact splice_old_branch_fixed _ ((unitSpliceMolIsoMk γ Z σ hT hsel).e b)
  change n.1.2.getLast hn = i
  exact (spliceOldNode_port l n hn ho hf).trans (node_last_of_eq_child _ ho v i he)


/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_eq`). -/
theorem unitSpliceChildSlot_eqMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt γ G σ Mk).G.tree) (i : Fin 3) : unitSpliceChildSlotMk γ Z σ hT hsel b i = i := by
  obtain ⟨j, hj, hext⟩ := spliceFold_outer_slot (unitBlocks γ G σ Mk)
    (unitBlocks_pairwiseMk (garden_isMolecule G) σ Mk) b
  have he := child_equiv_eq_refl (unitSpliceChildEquivMk γ Z σ hT hsel b)
    (unitSpliceChildSlot_middleMk Z σ hT hsel b) j hj (unitSpliceChildSlot_of_externalMk Z σ hT hsel b j hext)
  exact congrArg (fun e : Fin 3 ≃ Fin 3 => e i) he


end WaveTurbulence.GammaLow.Fama.VineA

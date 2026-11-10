/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRepGap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizationNamesSupp
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepAudit
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDartAddress
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOrdered
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOuter
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit


/-!
R83 successor copy of pinned/r83-RepGap.lean (original SHA in COPIED-SHA256SUMS).

# S2 REPRESENTS, W1b: the spliced gap indicator is the `σ`-restriction

Restriction direction (no lift): for a conserving decoration `z` of the original garden `G` and ANY
labels `κsb = κ ∘ od` of `G_sb`, `splicedGapIndicator G_sb = [selOf γ σ z]` (TARGET L1950, L1956).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineA
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Every vine-like object has a gap (at its upper joint) for any labels. -/
theorem exists_hasGapKind {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : Src.Object γ M) {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (κ : D → (Fin d → ℤ)) : ∃ k, O.HasGapKind L γ' η v κ k := by
  classical
  cases hs : O.shape with
  | vc hv =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists M hv.1 (Or.inl rfl) L v κ
    refine ⟨_, r, ?_, rfl⟩
    unfold Src.VineLikeObject.IsGap
    rw [hs]; exact hr
  | hyper R =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists (Mole.eraseBond M R.added) R.adjoint.1 (Or.inl rfl)
      L v (fun x => κ x.1)
    refine ⟨_, r, ?_, rfl⟩
    unfold Src.VineLikeObject.IsGap
    rw [hs]; exact hr


/-- `groupGapKind` is the kind of the designated object for any labels (the object always has a gap). -/
theorem exists_groupGapKind_eq {G : Garden w} {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) {S : Finset (GBranch G.tree)} {O : Src.Object γ G.molecule}
    (hO : designatedObject γ G S = some O) :
    ∃ k, O.HasGapKind L γ' η v κ k ∧ groupGapKind γ G L γ' η v κ S = k := by
  obtain ⟨k, hk⟩ := exists_hasGapKind O L γ' η v κ
  exact ⟨k, hk, groupGapKind_eq L γ' η v κ hO hk⟩

open scoped Classical in
/-- **W1b.** For a conserving decoration `κ = bondIndex G z` of the original garden and labels `κsb = κ ∘ od` of
`G_sb`, the spliced gap indicator (any kernel data carrying `gapSpecification γ G σ`) is the indicator of the
`σ`-restriction `selOf` (TARGET L1950, L1956). -/
theorem splicedGapIndicator_eq_selOf (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (L γ' η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt γ G σ).G zsb y = bondIndex G z ((stSt γ G σ).M.od y))
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = gapSpecification γ G σ) :
    splicedGapIndicator (stSt γ G σ).G D L γ' η base zsb =
      if selOf γ (GroupPrescription.ofPrescription γ σ) L γ' η base z then 1 else 0 := by
  classical
  set Q : GBranch (stSt γ G σ).G.tree → Prop := fun v => ∀ q, gapSpecification γ G σ v = some q →
        Molecule.gapKind L γ' η ((base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.second))) = q.kind with hQ
  have hf : splicedGapIndicator (stSt γ G σ).G D L γ' η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold splicedGapIndicator
    rw [hD]
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (stSt γ G σ).G.tree))) (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ' η ((base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ selOf γ (GroupPrescription.ofPrescription γ σ) L γ' η base z := by
    constructor
    · intro hall
      unfold selOf
      intro S
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ S.2 L γ' η base c _ hκ hc0
        (bondIndex (stSt γ G σ).G zsb) hlab
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ' η base (bondIndex G z) hO
      have := (hind k hk).mp (hall _ e he)
      exact hgk.trans this
    · intro hsel v q hq
      have hsome : (gapSpecification γ G σ v).isSome := by rw [hq]; rfl
      obtain ⟨S, hS, hSv⟩ := (gapSpecification_isSome_iff hM σ v).mp hsome
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ hS L γ' η base c _ hκ hc0
        (bondIndex (stSt γ G σ).G zsb) hlab
      have hat : groupAtom γ G σ S = some ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) := by
        unfold groupAtom; rw [ha]; rfl
      rw [hat] at hSv
      cases hSv
      rw [he] at hq
      cases hq
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ' η base (bondIndex G z) hO
      exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

open scoped Classical in
/-- `splicedGapIndicator_eq_selOf` for a garden decoration `z` with root values `roots` of a plain garden. -/
theorem splicedGapIndicator_eq_selOf_gen (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ' η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (zsb : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt γ G σ).G zsb y = bondIndex G z.1 ((stSt γ G σ).M.od y))
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = gapSpecification γ G σ) :
    splicedGapIndicator (stSt γ G σ).G D L γ' η base zsb =
      if selOf γ (GroupPrescription.ofPrescription γ σ) L γ' η base z.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOf hM σ L γ' η base _ z.1 (spliced_molecule_decoration G hp hL base roots z)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv) zsb hlab D hD

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice

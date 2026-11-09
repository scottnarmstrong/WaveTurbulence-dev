/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossIsoR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossR83
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
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
-- R83 port of sp-src/SubproCross.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): the contained darts of an object at a joint (R28 session 2, `crossing`)
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
  WaveTurbulence.Stage1 WaveTurbulence.Mole
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem contained_unique {w : ℕ} (G' : Garden w) (P : Src.Object γ G'.molecule) {v : GBranch G'.tree}
    (hv : v = P.upper ∨ v = P.lower) (b : Bool) :
    ∃ x, G'.molecule.atom x = v ∧ P.ContainsDart x ∧ G'.molecule.out x = b ∧
      ∀ x', G'.molecule.atom x' = v → P.ContainsDart x' → G'.molecule.out x' = b → x' = x := by
  obtain ⟨A, a, c, sh⟩ := P
  simp only at hv
  cases sh with
  | vc h =>
    have hB : G'.molecule.IsBlock A a c := h.1
    have hB' : ∃ c', G'.molecule.IsBlock A v c' := by
      rcases hv with rfl | rfl
      · exact ⟨c, hB⟩
      · exact ⟨a, block_swap_joints _ hB⟩
    obtain ⟨c', hc'⟩ := hB'
    obtain ⟨x, h1, h2, h3, h4⟩ := block_unique_dart hc' b
    exact ⟨x, h1, h2, h3, fun x' h1' h2' h3' => h4 x' h1' h2' h3'⟩
  | hyper R =>
    have hB : (Mole.eraseBond G'.molecule R.added).IsBlock A a c := R.adjoint.1
    have hB' : ∃ c', (Mole.eraseBond G'.molecule R.added).IsBlock A v c' := by
      rcases hv with rfl | rfl
      · exact ⟨c, hB⟩
      · exact ⟨a, block_swap_joints _ hB⟩
    obtain ⟨c', hc'⟩ := hB'
    obtain ⟨x, h1, h2, h3, h4⟩ := block_unique_dart hc' b
    refine ⟨x.1, h1, ⟨x.2.1, x.2.2, h2⟩, h3, ?_⟩
    intro x' h1' h2' h3'
    have := h4 ⟨x', h2'.1, h2'.2.1⟩ h1' h2'.2.2 h3'
    exact congrArg Subtype.val this

variable {R : ℕ} {G : Garden (2 * R)}

/-- **The two inside darts of `P` at a hinge sit at one common joint of the unit** (the hinge pair is not split by `P`). -/
theorem hinge_common_joint (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (P : Src.Object γ (stSt γ G σ).G.molecule) {v : GBranch (stSt γ G σ).G.tree} (hvh : v ∈ (stSt γ G σ).hinges)
    (hvj : v = P.upper ∨ v = P.lower)
    (hnx : ∀ x y, Fama.VineA.NormalizedSplice.hingePair γ G σ v = some (x, y) → (P.ContainsDart x ↔ P.ContainsDart y)) :
    ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob v = u.upper ∧ ∃ j, (j = u.upper ∨ j = u.lower) ∧
      ∀ x, (stSt γ G σ).G.molecule.atom x = v → P.ContainsDart x → G.molecule.atom ((stSt γ G σ).M.od x) = j := by
  classical
  obtain ⟨x, y, hp, hPP, -⟩ := Fama.VineA.NormalizedSplice.hingePair_spec hM σ hvh
  have hnx' := hnx x y hp
  obtain ⟨hT, u, hu, hob, jc, hjc, hxj, hyj, hxe, hye⟩ := hPP
  obtain ⟨ao, hao, hao_c, hao_o, hao_u⟩ := contained_unique (stSt γ G σ).G P hvj true
  obtain ⟨ai, hai, hai_c, hai_o, hai_u⟩ := contained_unique (stSt γ G σ).G P hvj false
  have main : ∀ oc ic : GardenDart (stSt γ G σ).G, G.molecule.atom ((stSt γ G σ).M.od oc) = jc →
      G.molecule.atom ((stSt γ G σ).M.od ic) = jc → ¬ G.molecule.InGroup u.atoms ((stSt γ G σ).M.od oc) →
      ¬ G.molecule.InGroup u.atoms ((stSt γ G σ).M.od ic) → (stSt γ G σ).G.molecule.out oc = true →
      (stSt γ G σ).G.molecule.out ic = false → (P.ContainsDart oc ↔ P.ContainsDart ic) →
      (stSt γ G σ).G.molecule.atom oc = v → (stSt γ G σ).G.molecule.atom ic = v →
      ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ G σ).M.od ao) = j ∧
        G.molecule.atom ((stSt γ G σ).M.od ai) = j := by
    intro oc ic hoc hic hoe hie hoo hio hiff hoa hia
    refine common_joint hM σ hu hob hjc hoc hic hoe hie hoo hio hao hai hao_o hai_o ?_
    by_cases hc : P.ContainsDart oc
    · exact Or.inl ⟨(hao_u oc hoa hc hoo).symm, (hai_u ic hia (hiff.mp hc) hio).symm⟩
    · refine Or.inr ⟨fun h => hc (h ▸ hao_c), fun h => (fun hc' => hc (hiff.mpr hc')) (h ▸ hai_c)⟩
  have hout : (stSt γ G σ).G.molecule.out x ≠ (stSt γ G σ).G.molecule.out y := hT.2.2.2
  obtain ⟨j, hj, hjao, hjai⟩ : ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ G σ).M.od ao) = j ∧
      G.molecule.atom ((stSt γ G σ).M.od ai) = j := by
    cases hox : (stSt γ G σ).G.molecule.out x
    · have hoy : (stSt γ G σ).G.molecule.out y = true := by
        cases hoy' : (stSt γ G σ).G.molecule.out y
        · exact absurd (hox.trans hoy'.symm) hout
        · rfl
      exact main y x hyj hxj hye hxe hoy hox hnx'.symm hT.2.1 hT.1
    · have hoy : (stSt γ G σ).G.molecule.out y = false := by
        cases hoy' : (stSt γ G σ).G.molecule.out y
        · rfl
        · exact absurd (hox.trans hoy'.symm) hout
      exact main x y hxj hyj hxe hye hox hoy hnx' hT.1 hT.2.1
  refine ⟨u, hu, hob, j, hj, ?_⟩
  intro x' hx' hc'
  cases hox : (stSt γ G σ).G.molecule.out x'
  · rw [hai_u x' hx' hc' hox]; exact hjai
  · rw [hao_u x' hx' hc' hox]; exact hjao

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro

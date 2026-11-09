/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryR83
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
-- R83 port of sp-src/SubproEntry.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): the entry of a group of `𝒞` lies inside the `C_1` object of the group

For a group `S` with an SG object `O` of `C_1`, the gap-specification entry at `π a` (`a = Fama.VineA.NormalizedSplice.groupJoint γ G S`) is a pair of
darts inside `O` at one of its Fama.ChainL.joints (HV: the designated object and `O` share the canonical triple `Fama.VineA.hvGroupPick`; skipped
vine: `Fama.VineA.NormalizedSplice.HingeSpec` at a hinge, or `L0 = ∅` and the darts of the block at `x` are the darts of the vine).
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

/-- B1b (Mk-general form of `atom_eq_pi`). -/
theorem atom_eq_piMk (σ : Prescription G) {Mk : Set (CLVineG γ _)} (f : GardenDart (stSt γ (Mk := Mk) G σ).G) :
    (stSt γ (Mk := Mk) G σ).G.molecule.atom f = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od f)) ∧
    (stSt γ (Mk := Mk) G σ).G.molecule.atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate f) =
      (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls (G.molecule.atom (G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od f))) := by
  constructor
  · apply (stSt γ (Mk := Mk) G σ).M.ob_inj
    rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, (stSt γ (Mk := Mk) G σ).M.ob_atom]
  · apply (stSt γ (Mk := Mk) G σ).M.ob_inj
    rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, (stSt γ (Mk := Mk) G σ).M.ob_atom, (stSt γ (Mk := Mk) G σ).M.od_mate]

theorem atom_eq_pi (σ : Prescription G) (f : GardenDart (stSt γ G σ).G) :
    (stSt γ G σ).G.molecule.atom f = (stSt γ G σ).M.pi (stSt γ G σ).hcls (G.molecule.atom ((stSt γ G σ).M.od f)) ∧
    (stSt γ G σ).G.molecule.atom ((stSt γ G σ).G.molecule.mate f) =
      (stSt γ G σ).M.pi (stSt γ G σ).hcls (G.molecule.atom (G.molecule.mate ((stSt γ G σ).M.od f))) := atom_eq_piMk (Mk := ∅) σ f

/-- B1b (Mk-general form of `containsDart_of_orig`). -/
theorem containsDart_of_origMk (σ : Prescription G) {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls)) {f : GardenDart (stSt γ (Mk := Mk) G σ).G}
    (hf : G.molecule.InGroup A ((stSt γ (Mk := Mk) G σ).M.od f))
    (hsh : ∀ R, O.shape = Src.VineLikeObject.hyper R →
      (stSt γ (Mk := Mk) G σ).M.od f ≠ (stSt γ (Mk := Mk) G σ).M.od R.added ∧
        (stSt γ (Mk := Mk) G σ).M.od f ≠ G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od R.added)) : O.ContainsDart f := by
  have hg : (stSt γ (Mk := Mk) G σ).G.molecule.InGroup O.atoms f := by
    obtain ⟨h1, h2⟩ := atom_eq_piMk (Mk := Mk) σ f
    rw [hOa]
    exact ⟨by rw [h1]; exact Finset.mem_image_of_mem _ hf.1, by rw [h2]; exact Finset.mem_image_of_mem _ hf.2⟩
  unfold Src.Object.ContainsDart
  cases hs : O.shape with
  | vc _ => exact hg
  | hyper R' =>
    obtain ⟨n1, n2⟩ := hsh R' hs
    refine ⟨fun h => n1 (by rw [h]), fun h => n2 ?_, hg⟩
    rw [← (stSt γ (Mk := Mk) G σ).M.od_mate, h]

/-- A dart of `G_sb` whose original dart lies in `A` is inside the object with atoms `π''A`. -/
theorem containsDart_of_orig (σ : Prescription G) {O : Src.Object γ (stSt γ G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls)) {f : GardenDart (stSt γ G σ).G}
    (hf : G.molecule.InGroup A ((stSt γ G σ).M.od f))
    (hsh : ∀ R, O.shape = Src.VineLikeObject.hyper R →
      (stSt γ G σ).M.od f ≠ (stSt γ G σ).M.od R.added ∧
        (stSt γ G σ).M.od f ≠ G.molecule.mate ((stSt γ G σ).M.od R.added)) : O.ContainsDart f := containsDart_of_origMk (Mk := ∅) σ hOa hf hsh


end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro

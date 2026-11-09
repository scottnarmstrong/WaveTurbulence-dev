/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRepSel` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.Spine.SourceGapTableObjects
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRepSel
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport


/-!
R83 successor copy of pinned/r83-RepSel.lean (original SHA in COPIED-SHA256SUMS).

# S2 REPRESENTS, W1: the gap kind of a group and the `σ`-restriction `sel`

TARGET L1950: the sum over a congruence class is split by specifying for every vine-like object of `𝒞` whether it
is SG, LG or ZG; this is "an extra restriction on the decoration" (the factor `Z`).  Here:
* `designatedObject γ G S` (redsplice, R25(a)): the designated vine-like object of the group `S`;
* `groupGapKind`: the gap kind of that object under a decoration (unique, `Object.hasGapKind_unique`);
* `GroupPrescription γ G`: SG/LG/ZG on the groups only (RULINGS R24 D2);
* `selOf γ σ`: the decorations whose group gap kinds are `σ`; `selOf_unique`, `exists_unique_prescription`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.RedSplice

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- SG/LG/ZG prescriptions on the groups of `𝒞` only (R24 D2). -/
abbrev GroupPrescription (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) := {S : Finset (GBranch G.tree) // S ∈ maximalGroupsG γ G.molecule} → Molecule.GapKind

/-- The restriction of a total prescription to the groups. -/
@[expose] def GroupPrescription.ofPrescription {G : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (σ : Prescription G) : GroupPrescription γ G := fun S => σ S.1



/-- The gap kind of the group `S` under the decoration `κ` (momentum offset `v`): that of its designated
object; `ZG` if the group has no designated object or no gap (irrelevant for groups of `𝒞`). -/
@[expose] noncomputable def groupGapKind (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (S : Finset (GBranch G.tree)) : Molecule.GapKind := by
  classical
  exact if h : ∃ O, designatedObject γ G S = some O ∧ ∃ k, O.HasGapKind L γ' η v κ k then h.choose_spec.2.choose
  else .ZG


/-- **The `σ`-restriction on decorations** (TARGET L1950, factor `Z`): the group gap kinds of the
decoration `z` of the garden `G` are `σ`. -/
@[expose] def selOf {G : Garden w} {d : ℕ} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (σ : GroupPrescription γ G) (L γ' η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : Prop :=
  ∀ S : {S : Finset (GBranch G.tree) // S ∈ maximalGroupsG γ G.molecule},
    groupGapKind γ G L γ' η v (bondIndex G z) S.1 = σ S

/-- The prescription of a decoration. -/
@[expose] noncomputable def prescriptionOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : GroupPrescription γ G :=
  fun S => groupGapKind γ G L γ' η v (bondIndex G z) S.1

theorem selOf_prescriptionOf {G : Garden w} {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : selOf γ (prescriptionOf γ G L γ' η v z) L γ' η v z := fun _ => rfl

/-- **Uniqueness**: a decoration satisfies the restriction of exactly one group prescription. -/
theorem selOf_unique {G : Garden w} {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) {σ τ : GroupPrescription γ G}
    (hσ : selOf γ σ L γ' η v z) (hτ : selOf γ τ L γ' η v z) : σ = τ :=
  funext fun S => (hσ S).symm.trans (hτ S)

theorem exists_unique_prescription {G : Garden w} {d : ℕ} (L γ' η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ∃! σ : GroupPrescription γ G, selOf γ σ L γ' η v z :=
  ⟨prescriptionOf γ G L γ' η v z, selOf_prescriptionOf L γ' η v z, fun _ h => selOf_unique L γ' η v z h
    (selOf_prescriptionOf L γ' η v z)⟩

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice

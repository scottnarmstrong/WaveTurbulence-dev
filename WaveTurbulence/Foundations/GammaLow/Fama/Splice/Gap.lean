/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceGap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGap


/-!
# REDSPLICE-DEF (S2a): the gap specification of `G_sb` (TARGET L1956, L1963; the factor `Z`)

(R25) Each group `S` of `𝒞` carries one entry at its designated atom `π a` (`a = groupJoint γ G S`), of kind `σ S`.
The pair of darts of the entry is the lift to `G_sb` of a pair of darts of the ORIGINAL garden that was chosen once,
independently of `σ` (`RedSpliceDesig`):
* if `π a` is not a hinge: `intPairOrig γ G S`, a pair inside the designated object `designatedObject γ G S` at its joint;
* if `π a` is a hinge (`a` lies in a spliced unit): `hingeOrigPair γ G S`, a pair of the skipped vine at its joint, or the
  external pair at a degree-four joint of the whole-group unit.
`gapSpecification` is the resulting `Option`-valued function on the atoms of `G_sb`.  The theorems
`gapSpecification_group`, `gapSpecification_pair_of_object` and `gapSpecification_hinge_kind` show that every group has
its entry, of kind `σ S`, whose darts are (images of) the chosen original pair; hinge entries are SG.
The hinge pair `hingePair` of `collectionChoices` (the `C_1` data of subpro(5)) is separate and unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The internal pair at a non-hinge designated atom: the lift of `intPairOrig`. -/
@[expose] noncomputable def internalPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) :=
  (intPairOrig γ G S Mk).bind (liftPair γ G σ v)

/-- The pair of darts of the entry of the group `S` at `v`. -/
@[expose] noncomputable def gapPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) := by
  classical exact if v ∈ (stSt γ G σ Mk).hinges then hingeEntryPair γ G σ S v else internalPair γ G σ S v

/-- **The gap specification of `G_sb`** (the indicator `Z` of TARGET L1956, L1963), for the marked vine set `Mk`
(B1a).  B2c (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry at the image of its upper
joint (`MarkedEntryAt`), with the lift of the chosen pair of `t` there and the kind `σ S`. -/
@[expose] noncomputable def gapSpecificationMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G))
    (v : GBranch (stSt γ G σ Mk).G.tree) : Option (LocalGapSpecification (stSt γ G σ Mk).G v) := by
  classical
  exact if h : ∃ S ∈ maximalGroupsG γ G.molecule, groupAtom γ G σ S Mk = some v then
    (match gapPair γ G σ h.choose v with
      | some p => if hp : TripleAt (stSt γ G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h.choose⟩ else none
      | none => none)
  else if h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ maximalGroupsG γ G.molecule ∧ MarkedEntryAt γ G σ St.1 St.2 v then
    (match markedEntryPair γ G σ h'.choose.2 v with
      | some p => if hp : TripleAt (stSt γ G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h'.choose.1⟩ else none
      | none => none)
  else none

end WaveTurbulence.GammaLow.Fama

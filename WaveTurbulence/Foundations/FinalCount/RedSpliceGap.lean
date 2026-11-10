/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the gap specification of `G_sb` (TARGET L1956, L1963; the factor `Z`)

(R25) Each group `S` of `𝒞` carries one entry at its designated atom `π a` (`a = groupJoint G S`), of kind `σ S`.
The pair of darts of the entry is the lift to `G_sb` of a pair of darts of the ORIGINAL garden that was chosen once,
independently of `σ` (`RedSpliceDesig`):
* if `π a` is not a hinge: `intPairOrig G S`, a pair inside the designated object `designatedObject G S` at its joint;
* if `π a` is a hinge (`a` lies in a spliced unit): `hingeOrigPair G S`, a pair of the skipped vine at its joint, or the
  external pair at a degree-four joint of the whole-group unit.
`gapSpecification` is the resulting `Option`-valued function on the atoms of `G_sb`.  The theorems
`gapSpecification_group`, `gapSpecification_pair_of_object` and `gapSpecification_hinge_kind` show that every group has
its entry, of kind `σ S`, whose darts are (images of) the chosen original pair; hinge entries are SG.
The hinge pair `hingePair` of `collectionChoices` (the `C_1` data of subpro(5)) is separate and unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The internal pair at a non-hinge designated atom: the lift of `intPairOrig`. -/
@[expose] noncomputable def internalPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (intPairOrig G S Mk).bind (liftPair G σ v)

/-- The pair of darts of the entry of the group `S` at `v`. -/
@[expose] noncomputable def gapPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical exact if v ∈ (stSt G σ Mk).hinges then hingeEntryPair G σ S v else internalPair G σ S v

/-- **The gap specification of `G_sb`** (the indicator `Z` of TARGET L1956, L1963), for the marked vine set `Mk`
(B1a).  B2c (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry at the image of its upper
joint (`MarkedEntryAt`), with the lift of the chosen pair of `t` there and the kind `σ S`. -/
@[expose] noncomputable def gapSpecificationMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G))
    (v : GBranch (stSt G σ Mk).G.tree) : Option (LocalGapSpecification (stSt G σ Mk).G v) := by
  classical
  exact if h : ∃ S ∈ maximalGroups G.molecule, groupAtom G σ S Mk = some v then
    (match gapPair G σ h.choose v with
      | some p => if hp : TripleAt (stSt G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h.choose⟩ else none
      | none => none)
  else if h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ maximalGroups G.molecule ∧ MarkedEntryAt G σ St.1 St.2 v then
    (match markedEntryPair G σ h'.choose.2 v with
      | some p => if hp : TripleAt (stSt G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h'.choose.1⟩ else none
      | none => none)
  else none

end WaveTurbulence.RedSplice

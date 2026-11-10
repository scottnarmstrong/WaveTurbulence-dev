/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceColl2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl2


/-!
# REDSPLICE-DEF (S2a), B: `Src.SubproChoices γ` of `G_sb`

`objects γ G σ`: the objects γ of `C_1`; `ProperPair`.  (R28: `hingePair`, `collectionChoices` and their theorems moved
to `RedSpliceHingePair`, after the designated pairs of `RedSpliceDesig`.)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The object of the SG group `S` in `G_sb` (if it contributes one). -/
@[expose] noncomputable def objOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVineG γ G) := ∅) : Option (Src.Object γ (stSt γ G σ Mk).G.molecule) := by
  classical
  exact if h : G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj γ G S ∧
      ¬ markedGroup γ G Mk S ∧ ∃ O : Src.Object γ (stSt γ G σ Mk).G.molecule, ObjSpecMk γ G σ S Mk O then
    some (Classical.choose h.2.2.2.2.2) else none

/-- The objects γ of `C_1`.  B1a: with the marked vine set `Mk` (default `∅`), the objects γ of the unmarked SG groups
(o75: `𝒞₁` = main's objects γ restricted to `¬ markedGroup`). -/
@[expose] noncomputable def objects (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) :
    List (Src.Object γ (stSt γ G σ Mk).G.molecule) :=
  (sgGroups γ G σ).filterMap (fun S => objOf γ G σ S Mk)

/-- A **proper hinge pair** at the hinge `v` is the lift of an external out/in pair of a unit (the unit whose crown
is `v`) at one of its joints (TARGET `subpro` (5): "the two bonds at one joint of `U` that do not belong to `U`"). -/
@[expose] def ProperPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree)
    (x y : GardenDart (stSt γ G σ Mk).G) : Prop :=
  TripleAt (stSt γ G σ Mk).G v x y ∧ ∃ u ∈ unitBlocks γ G σ Mk, (stSt γ G σ Mk).M.ob v = u.upper ∧
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ G σ Mk).M.od x) = j ∧
      G.molecule.atom ((stSt γ G σ Mk).M.od y) = j ∧
      ¬ G.molecule.InGroup u.atoms ((stSt γ G σ Mk).M.od x) ∧ ¬ G.molecule.InGroup u.atoms ((stSt γ G σ Mk).M.od y)

end WaveTurbulence.GammaLow.Fama

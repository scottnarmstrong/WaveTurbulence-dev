/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair


/-!
# REDSPLICE-DEF (S2a), R28: the hinge pairs and the choice data `C_1` of `G_sb`

(R28) `hingePair γ G σ v`, the pair `(ℓ_1, ℓ_2)` of TARGET subpro(5) at the hinge `v` (always a `ProperPair`, i.e. the lift of an
external out/in pair of the unit with crown `v` at one of its joints):
1. if `v` is the designated atom of a group `S`: the LIFT of `hingeOrigPair` of `S` (so `Cs.first/second` is the entry pair of
   `gapSpecification` at `v`);
2. otherwise the lift of a pair `HingeSpec γ G S u.upper p` of the unit `u` with crown `v` (for a hinge of a skipped vine
   it lies inside the residual object);
3. otherwise a proper pair.
0. (B2c, o75 Theorem 7.5′(5) and 75-F1, taken first) at a joint of a survivor: the lift of the pair of the survivor
   removed first (`survPairAt`).
`collectionChoices γ G σ`, `structural_collectionChoices`, `hingeOutsideFirst_collectionChoices`: as before.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The designated atom of the group `S` in `G_sb`. -/
@[expose] noncomputable def groupAtom (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVineG γ G) := ∅) : Option (GBranch (stSt γ G σ Mk).G.tree) :=
  (groupJoint γ G S Mk).map ((stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls)

/-- The lift to `G_sb` (at the atom `v`) of a pair of darts of the original garden: darts of `G_sb` whose images
under `od` are the given darts and which form a `TripleAt` at `v`. -/
@[expose] noncomputable def liftPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (v : GBranch (stSt γ G σ Mk).G.tree)
    (p : GardenDart G × GardenDart G) : Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) := by
  classical
  exact if h : ∃ q : GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G,
      (stSt γ G σ Mk).M.od q.1 = p.1 ∧ (stSt γ G σ Mk).M.od q.2 = p.2 ∧ TripleAt (stSt γ G σ Mk).G v q.1 q.2
  then some (Classical.choose h) else none

/-- The pair at a hinge designated atom: the lift of `hingeOrigPair`. -/
@[expose] noncomputable def hingeEntryPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) :=
  (hingeOrigPair γ G S Mk).bind (liftPair γ G σ v)

/-- B1a (o75 Theorem 7.5′ clause (5)): a hinge pair of a run `u` of a marked group: an out/in pair of darts of the
original garden at an outer joint of `u`, both external to `u`.  (The 75-F1 rule, which prefers among these the
bonds of the survivor removed first, is a marked-group branch of B2c.) -/
@[expose] def HingeSpecRun (G : Garden w) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j, (j = u.upper ∨ j = u.lower) ∧ TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧
    ¬ G.molecule.InGroup u.atoms p.2

/-- B2c (o75 Theorem 7.5′(5), 75-F1): the first survivor (in `survivorsMk` order, i.e. chain by chain along the spine)
having a joint at `v` in `G_sb`, with that joint (its lower joint if both map to `v`). -/
@[expose] noncomputable def survJointAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (v : GBranch (stSt γ G σ Mk).G.tree) : Option (Finset (GBranch G.tree) × GBranch G.tree) := by
  classical
  exact ((survivorsMk γ G σ Mk).find? (fun t => decide ((stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls t.2.2 = v ∨
      (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls t.2.1 = v))).map
    (fun t => (t.1, if (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls t.2.2 = v then t.2.2 else t.2.1))

/-- B2c (75-F1): the designated pair at a joint `v` of a survivor (hinge or not): the lift of the pair, at that joint,
of the survivor removed first. -/
@[expose] noncomputable def survPairAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (v : GBranch (stSt γ G σ Mk).G.tree) : Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) :=
  (survJointAt γ G σ v).bind fun Tj => (survOrigPair G Tj.1 Tj.2).bind (liftPair γ G σ v)

/-- B2c (ruling R171, o75 (2.3)): `v` carries the gap entry of the survivor `t` of the group `S`, i.e. `v` is the
image in `G_sb` of the upper joint of `t`.  Every survivor of a marked group carries an entry (of the group's kind), so
the indicator `𝒵` checks the gap of every survivor on any decoration of `G_sb`. -/
@[expose] def MarkedEntryAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) {Mk : Set (CLVineG γ G)}
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) (v : GBranch (stSt γ G σ Mk).G.tree) : Prop :=
  t ∈ groupSurvMk γ G Mk S ∧ (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls t.2.1 = v

/-- B2c (R171): the pair of the gap entry of the survivor `t` at `v`: the lift of the chosen pair of `t` at its upper
joint. -/
@[expose] noncomputable def markedEntryPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) :=
  (survOrigPair G t.1 t.2.1).bind (liftPair γ G σ v)

/-- **The hinge pair of TARGET subpro(5)** (R28): see the module docstring.  B1a: with the marked vine set `Mk`
the units are `groupUnitsMk` (runs in a marked group, with the run pair `HingeSpecRun`). -/
@[expose] noncomputable def hingePair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) := by
  classical
  exact if h0 : ∃ q, survPairAt γ G σ v = some q then some (Classical.choose h0)
  else if h : ∃ p : GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G, ∃ S ∈ maximalGroupsG γ G.molecule,
      groupAtom γ G σ S Mk = some v ∧ hingeEntryPair γ G σ S v = some p ∧ ProperPair γ G σ v p.1 p.2
  then some (Classical.choose h)
  else if h2 : ∃ q : GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G, ∃ S ∈ maximalGroupsG γ G.molecule,
      ∃ u ∈ groupUnitsMk γ G Mk S, (stSt γ G σ Mk).M.ob v = u.upper ∧
        ∃ p, (¬ markedGroup γ G Mk S → HingeSpec γ G S u.upper p) ∧ (markedGroup γ G Mk S → HingeSpecRun G u p) ∧
          liftPair γ G σ v p = some q ∧ ProperPair γ G σ v q.1 q.2
  then some (Classical.choose h2)
  else if h3 : ∃ p : GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G, ProperPair γ G σ v p.1 p.2
  then some (Classical.choose h3) else none

/-- **The choice data `C_1`, hinges and hinge pairs of `G_sb`.**  B1a: trailing marked vine set `Mk` (default `∅`). -/
@[expose] noncomputable def collectionChoices (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) :
    Src.SubproChoices γ (stSt γ G σ Mk).G where
  count := (objects γ G σ Mk).length
  collection := fun i => (objects γ G σ Mk).get i
  hinges := (stSt γ G σ Mk).hinges
  first := fun v => (hingePair γ G σ v).map Prod.fst
  second := fun v => (hingePair γ G σ v).map Prod.snd


section cases
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end cases

section pairs
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end pairs

end WaveTurbulence.GammaLow.Fama

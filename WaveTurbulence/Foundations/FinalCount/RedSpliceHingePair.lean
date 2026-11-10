/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceDesig
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R28: the hinge pairs and the choice data `C_1` of `G_sb`

(R28) `hingePair G σ v`, the pair `(ℓ_1, ℓ_2)` of TARGET subpro(5) at the hinge `v` (always a `ProperPair`, i.e. the lift of an
external out/in pair of the unit with crown `v` at one of its joints):
1. if `v` is the designated atom of a group `S`: the LIFT of `hingeOrigPair` of `S` (so `Cs.first/second` is the entry pair of
   `gapSpecification` at `v`);
2. otherwise the lift of a pair `HingeSpec G S u.upper p` of the unit `u` with crown `v` (for a hinge of a skipped vine
   it lies inside the residual object);
3. otherwise a proper pair.
0. (B2c, o75 Theorem 7.5′(5) and 75-F1, taken first) at a joint of a survivor: the lift of the pair of the survivor
   removed first (`survPairAt`).
`collectionChoices G σ`, `structural_collectionChoices`, `hingeOutsideFirst_collectionChoices`: as before.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The designated atom of the group `S` in `G_sb`. -/
@[expose] noncomputable def groupAtom (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVine G) := ∅) : Option (GBranch (stSt G σ Mk).G.tree) :=
  (groupJoint G S Mk).map ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)

/-- The lift to `G_sb` (at the atom `v`) of a pair of darts of the original garden: darts of `G_sb` whose images
under `od` are the given darts and which form a `TripleAt` at `v`. -/
@[expose] noncomputable def liftPair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree)
    (p : GardenDart G × GardenDart G) : Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical
  exact if h : ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G,
      (stSt G σ Mk).M.od q.1 = p.1 ∧ (stSt G σ Mk).M.od q.2 = p.2 ∧ TripleAt (stSt G σ Mk).G v q.1 q.2
  then some (Classical.choose h) else none

/-- The pair at a hinge designated atom: the lift of `hingeOrigPair`. -/
@[expose] noncomputable def hingeEntryPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (hingeOrigPair G S Mk).bind (liftPair G σ v)

/-- B1a (o75 Theorem 7.5′ clause (5)): a hinge pair of a run `u` of a marked group: an out/in pair of darts of the
original garden at an outer joint of `u`, both external to `u`.  (The 75-F1 rule, which prefers among these the
bonds of the survivor removed first, is a marked-group branch of B2c.) -/
@[expose] def HingeSpecRun (G : Garden w) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j, (j = u.upper ∨ j = u.lower) ∧ TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧
    ¬ G.molecule.InGroup u.atoms p.2

/-- B2c (o75 Theorem 7.5′(5), 75-F1): the first survivor (in `survivorsMk` order, i.e. chain by chain along the spine)
having a joint at `v` in `G_sb`, with that joint (its lower joint if both map to `v`). -/
@[expose] noncomputable def survJointAt (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree) : Option (Finset (GBranch G.tree) × GBranch G.tree) := by
  classical
  exact ((survivorsMk G σ Mk).find? (fun t => decide ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 = v))).map
    (fun t => (t.1, if (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 = v then t.2.2 else t.2.1))

/-- B2c (75-F1): the designated pair at a joint `v` of a survivor (hinge or not): the lift of the pair, at that joint,
of the survivor removed first. -/
@[expose] noncomputable def survPairAt (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree) : Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (survJointAt G σ v).bind fun Tj => (survOrigPair G Tj.1 Tj.2).bind (liftPair G σ v)

/-- B2c (ruling R171, o75 (2.3)): `v` carries the gap entry of the survivor `t` of the group `S`, i.e. `v` is the
image in `G_sb` of the upper joint of `t`.  Every survivor of a marked group carries an entry (of the group's kind), so
the indicator `𝒵` checks the gap of every survivor on any decoration of `G_sb`. -/
@[expose] def MarkedEntryAt (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) {Mk : Set (CLVine G)}
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) (v : GBranch (stSt G σ Mk).G.tree) : Prop :=
  t ∈ groupSurvMk G Mk S ∧ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 = v

/-- B2c (R171): the pair of the gap entry of the survivor `t` at `v`: the lift of the chosen pair of `t` at its upper
joint. -/
@[expose] noncomputable def markedEntryPair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (survOrigPair G t.1 t.2.1).bind (liftPair G σ v)

/-- **The hinge pair of TARGET subpro(5)** (R28): see the module docstring.  B1a: with the marked vine set `Mk`
the units are `groupUnitsMk` (runs in a marked group, with the run pair `HingeSpecRun`). -/
@[expose] noncomputable def hingePair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical
  exact if h0 : ∃ q, survPairAt G σ v = some q then some (Classical.choose h0)
  else if h : ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
      groupAtom G σ S Mk = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2
  then some (Classical.choose h)
  else if h2 : ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
      ∃ u ∈ groupUnitsMk G Mk S, (stSt G σ Mk).M.ob v = u.upper ∧
        ∃ p, (¬ markedGroup G Mk S → HingeSpec G S u.upper p) ∧ (markedGroup G Mk S → HingeSpecRun G u p) ∧
          liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2
  then some (Classical.choose h2)
  else if h3 : ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ProperPair G σ v p.1 p.2
  then some (Classical.choose h3) else none

/-- **The choice data `C_1`, hinges and hinge pairs of `G_sb`.**  B1a: trailing marked vine set `Mk` (default `∅`). -/
@[expose] noncomputable def collectionChoices (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G) := ∅) :
    SubproChoices (stSt G σ Mk).G where
  count := (objects G σ Mk).length
  collection := fun i => (objects G σ Mk).get i
  hinges := (stSt G σ Mk).hinges
  first := fun v => (hingePair G σ v).map Prod.fst
  second := fun v => (hingePair G σ v).map Prod.snd

/-- B1b (Mk-general form of `structural_collectionChoices`). -/
theorem structural_collectionChoicesMk (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) {Mk : Set (Stage1.CLVine _)} : (collectionChoices (Mk := Mk) G σ).Structural := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, _, _, _, hS⟩ := mem_objectsMk (Mk := Mk) (List.get_mem (objects (Mk := Mk) G σ) i)
    exact hS.allowed
  · intro i j hne
    have hp := List.pairwise_iff_get.mp (objects_pairwiseMk (Mk := Mk) hM σ)
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hp i j h
    · exact (hp j i h).symm
  · intro a b hab
    exact (stSt (Mk := Mk) G σ).triple_hinge hno a b hab

/-- B1b (Mk-general form of `hingeOutsideFirst_collectionChoices`). -/
theorem hingeOutsideFirst_collectionChoicesMk (σ : Prescription G) {Mk : Set (Stage1.CLVine _)} :
    ∀ v ∈ (collectionChoices (Mk := Mk) G σ).hinges, ∀ i, ¬ ((collectionChoices (Mk := Mk) G σ).collection i).IsInterior v := by
  intro v hv i hint
  obtain ⟨_, _, _, _, hS⟩ := mem_objectsMk (Mk := Mk) (List.get_mem (objects (Mk := Mk) G σ) i)
  have hcn : (stSt (Mk := Mk) G σ).cls ((stSt (Mk := Mk) G σ).M.ob v) ≠ none := ((stSt (Mk := Mk) G σ).mem_hinges v).mp hv
  rcases hS.hinge v hcn hint.1 with h | h
  · exact hint.2.1 h
  · exact hint.2.2 h


section cases
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end cases

section pairs
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end pairs

end WaveTurbulence.RedSplice

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! Literal structural and decorated conclusions of TARGET subpro, L2040–L2051.
These predicates describe the output of the stage-one reduction; they do not assert the
reduction theorem or the disputed counting bound. Provider: S4 (SUBPRO). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset
variable {w d : ℕ}

/-- Two distinct bonds of opposite directions at one actual atom. -/
def TripleAt (G : Garden w) (v : GBranch G.tree) (x y : GardenDart G) : Prop :=
  G.molecule.atom x = v ∧ G.molecule.atom y = v ∧
    y ≠ G.molecule.mate x ∧ G.molecule.out x ≠ G.molecule.out y

/-- A partial source pair has actual values exactly where the source selects bonds. -/
def HasChosenPair {E : Type*} (first second : Option E) (P : E → E → Prop) : Prop :=
  ∃ x y, first = some x ∧ second = some y ∧ P x y

/-- The collection and hinge choices in subpro(2),(5), independent of the decoration. -/
structure SubproChoices (G : Garden w) where
  count : ℕ
  collection : Fin count → Object G.molecule
  hinges : Finset (GBranch G.tree)
  first : GBranch G.tree → Option (GardenDart G)
  second : GBranch G.tree → Option (GardenDart G)

/-- AMEND7 (R48): R37 / TARGET subpro (2),(5) and Operation 1 (L2140): every triple bond has a hinge endpoint
whose designated pair consists of two bonds of that triple bond (the conclusion of S4's
`Subpro.triple_in_designated`). -/
def SubproChoices.TripleDesignated {G : Garden w} (C : SubproChoices G) : Prop :=
  ∀ a b : GBranch G.tree, G.molecule.bondsBetween a b = 3 →
    ∃ v ∈ C.hinges, ∃ c x y, ((v = a ∧ c = b) ∨ (v = b ∧ c = a)) ∧
      C.first v = some x ∧ C.second v = some y ∧ TripleAt G v x y ∧
      G.molecule.atom (G.molecule.mate x) = c ∧ G.molecule.atom (G.molecule.mate y) = c

/-- AMEND7 (R48): no self-loop at a hinge (hinges carry no epsilon factor; `SpMap.od_range`). -/
def SubproChoices.HingeNoLoop {G : Garden w} (C : SubproChoices G) : Prop :=
  ∀ x : GardenDart G, G.molecule.atom x ∈ C.hinges →
    G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)

/-- TARGET subpro(2): disjoint allowed vine objects and hinges meeting every triple bond. -/
def SubproChoices.Structural {G : Garden w} (C : SubproChoices G) : Prop :=
  (∀ i, AllowedCollectionObject G (C.collection i)) ∧
  (∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms) ∧
  ∀ a b, G.molecule.bondsBetween a b = 3 → a ∈ C.hinges ∨ b ∈ C.hinges

/-- A small-gap object lies outside every selected object. -/
def SubproChoices.Outside {G : Garden w} (C : SubproChoices G) (P : Object G.molecule) : Prop :=
  ∀ i, ¬ P.IsContained (C.collection i)

/-- Atom-set version of `Outside` (R28 (3), TARGET L2040-L2051 "subset"): the atom set of `P` is contained in
no selected object's atom set. -/
def SubproChoices.OutsideAtoms {G : Garden w} (C : SubproChoices G) (P : Object G.molecule) : Prop :=
  ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms

/-- TARGET subpro(2)–(6), all decorated conditions for one surviving decoration. -/
structure SubproSupport (G : Garden w) (C : SubproChoices G) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) →
      G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → Disjoint P.atoms C.hinges →
    (∃ S a b, IsDV G.molecule S a b ∧ P.atoms ⊆ S ∧
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Object G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  crossing : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

end WaveTurbulence.LGSpine.SourceVine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.Spine.AnchorTypes
/-! # The finalcount1 counting choices over `𝒱_γ` (packet L6, FINALCOUNT-LOW)

A literal copy of main's `LGSpine.SourceVine` counting layer (`SourceSubproObjects`, `SourceCountingObjects`,
`SourceCanonicalDef`, `SourceCountingData`, `SourceFinalCountInputs`; sha256 in `COPIED-SHA256SUMS`, TARGET
L2040–L2053 and L2097–L2116), over the objects `Src.Object γ` of the family `𝒱_γ` (ruling D11). The only changes:
- objects, the subpro collection and the second collection are `Src.Object γ`;
- the double vine of TARGET L2101–L2104 is `DV′` (two `𝒱_γ` members with `σ = 1` sharing both joints).
Family-free helpers (`TripleAt`, `HasChosenPair`, `atomGapKind`, `IsDyadicScale`, `IsTame`, the spliced kernel
data and indicators) are main's, by import. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace WaveTurbulence.GammaLow.FinalCount.Src
open Set Finset
open WaveTurbulence.LGSpine
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale)
variable {w d : ℕ}

/-! ## subpro (TARGET L2040–L2051) -/

/-- The collection and hinge choices in subpro(2),(5), independent of the decoration. -/
structure SubproChoices (γ : ℝ) (G : Garden w) where
  count : ℕ
  collection : Fin count → Object γ G.molecule
  hinges : Finset (GBranch G.tree)
  first : GBranch G.tree → Option (GardenDart G)
  second : GBranch G.tree → Option (GardenDart G)

/-- AMEND7 (R48): every triple bond has a hinge endpoint whose designated pair consists of two of its bonds. -/
def SubproChoices.TripleDesignated {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) : Prop :=
  ∀ a b : GBranch G.tree, G.molecule.bondsBetween a b = 3 →
    ∃ v ∈ C.hinges, ∃ c x y, ((v = a ∧ c = b) ∨ (v = b ∧ c = a)) ∧
      C.first v = some x ∧ C.second v = some y ∧ TripleAt G v x y ∧
      G.molecule.atom (G.molecule.mate x) = c ∧ G.molecule.atom (G.molecule.mate y) = c

/-- AMEND7 (R48): no self-loop at a hinge. -/
def SubproChoices.HingeNoLoop {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) : Prop :=
  ∀ x : GardenDart G, G.molecule.atom x ∈ C.hinges →
    G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)

/-- TARGET subpro(2): disjoint allowed vine objects and hinges meeting every triple bond. -/
def SubproChoices.Structural {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) : Prop :=
  (∀ i, AllowedCollectionObject γ G (C.collection i)) ∧
  (∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms) ∧
  ∀ a b, G.molecule.bondsBetween a b = 3 → a ∈ C.hinges ∨ b ∈ C.hinges

/-- A small-gap object lies outside every selected object. -/
def SubproChoices.Outside {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) (P : Object γ G.molecule) : Prop :=
  ∀ i, ¬ P.IsContained (C.collection i)

/-- Atom-set version of `Outside` (R28 (3)). -/
def SubproChoices.OutsideAtoms {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) (P : Object γ G.molecule) : Prop :=
  ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms

/-- TARGET subpro(2)–(6), all decorated conditions for one surviving decoration (`DV` read as `DV′`). -/
structure SubproSupport (γ : ℝ) (G : Garden w) (C : SubproChoices γ G) (L γ' η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ' η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) →
      G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → C.OutsideAtoms P → Disjoint P.atoms C.hinges →
    (∃ S a b, IsDV γ G.molecule S a b ∧ P.atoms ⊆ S ∧
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Object γ G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ' η base κ .LG ∨ Q.HasGapKind L γ' η base κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ' η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  crossing : ∀ P : Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → C.OutsideAtoms P → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

/-! ## The second collection (TARGET L2101–L2104) -/

/-- The two constituents of a `DV′`: two members of `𝒱_γ` with `σ = 1`, sharing both joints and no other atom. -/
structure DoubleVine (γ : ℝ) (G : Garden w) where
  first : Finset (GBranch G.tree)
  second : Finset (GBranch G.tree)
  upper : GBranch G.tree
  lower : GBranch G.tree
  sigma_one : G.molecule.sigma upper lower = 1
  first_vine : IsSomeVine γ G.molecule first upper lower
  second_vine : IsSomeVine γ G.molecule second upper lower
  overlap : first ∩ second = {upper, lower}

/-- AMEND5 (R42(2)), atom-level eligibility (R28). -/
def eligibleSecondObject (γ : ℝ) (G : Garden w) (L γ' η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (P : Object γ G.molecule) : Prop :=
  P.HasGapKind L γ' η base κ .SG ∧
    ((∃ Q : Object γ G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ' η base κ .LG ∨ Q.HasGapKind L γ' η base κ .ZG) ∧
      Disjoint (↑Q.atoms : Set (GBranch G.tree)) F) ∨
      ∃ D : DoubleVine γ G, P.atoms ⊆ D.first ∪ D.second ∧
        Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F)

/-- Literal selection rule at TARGET L2101–L2104 (one constituent of an all-SG `DV′` omitted). -/
def IsSourceSecondCollection (γ : ℝ) (G : Garden w) (L γ' η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (Object γ G.molecule)) : Prop :=
  (∀ S ∈ omitted, ∃ D : DoubleVine γ G,
    Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F ∧
    (Object.ofVine D.first_vine).HasGapKind L γ' η base κ .SG ∧
    (Object.ofVine D.second_vine).HasGapKind L γ' η base κ .SG ∧
      (S = D.first ∨ S = D.second)) ∧
  (∀ D : DoubleVine γ G, Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F →
    (Object.ofVine D.first_vine).HasGapKind L γ' η base κ .SG →
    (Object.ofVine D.second_vine).HasGapKind L γ' η base κ .SG →
      Xor (D.first ∈ omitted) (D.second ∈ omitted)) ∧
  ∀ P : Object γ G.molecule, P ∈ collection ↔
    eligibleSecondObject γ G L γ' η base κ F P ∧ P.atoms ∉ omitted ∧
      ∀ Q : Object γ G.molecule, eligibleSecondObject γ G L γ' η base κ F Q → Q.atoms ∉ omitted →
        P.IsContained Q → Q.IsContained P

/-- Rank of the deleted bond of a hyper object; `0` for an ordinary object (unused). -/
def Object.hyperRank {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} {M : Molecule V D}
    (rk : D → ℕ) (P : Object γ M) : ℕ :=
  match P.shape with
  | .vc _ => 0
  | .hyper R => min (rk R.added) (rk (M.mate R.added))

/-- R6(a): the canonical part of a collection (least deleted-bond rank per hyper atom set). -/
def canonicalSub {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} {M : Molecule V D}
    (rk : D → ℕ) (K : Set (Object γ M)) : Set (Object γ M) :=
  {P | P ∈ K ∧ ∀ Q ∈ K, Q.atoms = P.atoms → (∃ R, P.shape = .hyper R) →
    (∃ R, Q.shape = .hyper R) → P.hyperRank rk ≤ Q.hyperRank rk}

/-! ## The counting choices (TARGET L2097–L2116) -/

/-- Fixed combinatorial and dyadic choices in requirements (b)–(f), over `𝒱_γ`. -/
structure CountingChoices (γ : ℝ) (G : Garden w) (d : ℕ) where
  subpro : SubproChoices γ G
  secondCollection : Set (Object γ G.molecule)
  omittedDVConstituents : Set (Finset (GBranch G.tree))
  atomLabel : GBranch G.tree → Molecule.GapKind
  first : GBranch G.tree → Option (GardenDart G)
  second : GBranch G.tree → Option (GardenDart G)
  atomScale : GBranch G.tree → ℝ
  ladderScale : Finset (GBranch G.tree) → ℝ
  fixedRoots : Finset (Mom d)

def CountingChoices.CriticalSG {γ : ℝ} {G : Garden w} (C : CountingChoices γ G d) (v : GBranch G.tree) : Prop :=
  C.atomLabel v = .SG ∧
    (∀ i, ¬ (C.subpro.collection i).IsInterior v) ∧
    ∀ P ∈ C.secondCollection, ¬ P.IsInterior v

noncomputable def CountingChoices.numCriticalSG {γ : ℝ} {G : Garden w} (C : CountingChoices γ G d) : ℕ := by
  classical
  exact ((univ : Finset (GBranch G.tree)).filter C.CriticalSG).card

/-- TARGET L2101–L2112 (R6(b)): the forbidden atoms of the restricted carrier. -/
def SubproChoices.forbidden {γ : ℝ} {G : Garden w} (C : SubproChoices γ G) : Set (GBranch G.tree) :=
  ↑C.hinges ∪ ⋃ i, (↑(C.collection i).atoms : Set (GBranch G.tree))

/-- R6(a),(b): the second collection is the canonical part of the literal collection of TARGET L2101–L2112. -/
def CountingChoices.SecondCollectionOK {γ : ℝ} {G : Garden w} (C : CountingChoices γ G d) (L γ' η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∃ rk : GardenDart G → ℕ, Function.Injective rk ∧ ∃ K : Set (Object γ G.molecule),
    IsSourceSecondCollection γ G L γ' η base κ C.subpro.forbidden C.omittedDVConstituents K ∧
    C.secondCollection = canonicalSub rk K

/-- Requirement (c): dyadic gap scales of every actual maximal ladder (family-free; as main). -/
def CountingChoices.LadderGaps {γ : ℝ} {G : Garden w} (C : CountingChoices γ G d) (L γ' η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∀ S ∈ G.molecule.maximalLadders,
    (C.ladderScale S = 0 ∨ (IsDyadicScale (C.ladderScale S) ∧
      L⁻¹ ≤ C.ladderScale S ∧ C.ladderScale S ≤ 1)) ∧
    ∃ m : ℕ, ∃ u v : Fin (m + 1) → GBranch G.tree, ∃ hm : 1 ≤ m,
      G.molecule.IsLadder u v ∧ Molecule.ladderAtoms u v = S ∧
      ∃ r, G.molecule.IsLadderGap L base κ u v hm r ∧
        (C.ladderScale S = 0 → r = 0) ∧
        (0 < C.ladderScale S → C.ladderScale S < 1 →
          C.ladderScale S / 2 ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * C.ladderScale S) ∧
        (C.ladderScale S = 1 → 1 ≤ ‖r‖)

/-- Structural consequences and fixed choices in requirements (b)–(f). -/
def CountingChoices.Admissible {γ : ℝ} {G : Garden w} (C : CountingChoices γ G d) (L γ' η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  SubproSupport γ G C.subpro L γ' η base C.fixedRoots κ ∧
  C.SecondCollectionOK L γ' η base κ ∧
  (∀ v, atomGapKind G L γ' η base κ v = C.atomLabel v) ∧
  (∀ v, C.atomLabel v = .SG → HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ' η (Molecule.gapAt L base κ x y) = .SG)) ∧
  (∀ v ∈ C.subpro.hinges, C.first v = C.subpro.first v ∧ C.second v = C.subpro.second v) ∧
  (∀ i v, (v = (C.subpro.collection i).upper ∨ v = (C.subpro.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      (C.subpro.collection i).ContainsDart x ∧ (C.subpro.collection i).ContainsDart y)) ∧
  (∀ P ∈ C.secondCollection, ∀ v, (v = P.upper ∨ v = P.lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
  (∀ v, C.CriticalSG v → IsDyadicScale (C.atomScale v) ∧
    L⁻¹ ≤ C.atomScale v ∧ C.atomScale v ≤ L ^ (-γ' + η) ∧
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      C.atomScale v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧
        ‖Molecule.gapAt L base κ x y‖ ≤ 2 * C.atomScale v)) ∧
  C.LadderGaps L γ' η base κ

/-- Source geometric typing: subpro(1),(2) and the hinge assertion after finalcount1 (TARGET L2116). -/
structure CountingGeometry {γ : ℝ} {R : ℕ} (G : Garden (2 * R)) (C : CountingChoices γ G d) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order
  subpro : C.subpro.Structural
  fixedRoots_card : C.fixedRoots.card ≤ 2 * R
  hingeSmall : ∀ v ∈ C.subpro.hinges, C.atomLabel v = .SG
  hingeOutsideFirst : ∀ v ∈ C.subpro.hinges, ∀ i, ¬ (C.subpro.collection i).IsInterior v
  hingeOutsideSecond : ∀ v ∈ C.subpro.hinges, ∀ P ∈ C.secondCollection, ¬ P.IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : C.subpro.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : C.subpro.HingeNoLoop

theorem CountingGeometry.hinges_card_le {γ : ℝ} {R : ℕ} {G : Garden (2 * R)} {C : CountingChoices γ G d}
    (h : CountingGeometry G C) : C.subpro.hinges.card ≤ C.numCriticalSG := by
  classical
  change C.subpro.hinges.card ≤ ((univ : Finset (GBranch G.tree)).filter C.CriticalSG).card
  apply Finset.card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, h.hingeSmall v hv,
    h.hingeOutsideFirst v hv, h.hingeOutsideSecond v hv⟩

/-- Literal `(k1,…,k2R)`-decorations of the spliced kernel satisfying requirements (b)–(f) (TARGET finalcount1),
over `𝒱_γ`. Requirement (a) is inside `Molecule.countE`. -/
def splicedCountingAdmissible {γ : ℝ} {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (C : CountingChoices γ G d) (L γ' η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  (∃ z : GenDecoration G d roots 0, (∀ x, bondIndex G z.1 x = κ x) ∧
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ' η base z.1 ≠ 0) ∧
  C.Admissible L γ' η base κ

end WaveTurbulence.GammaLow.FinalCount.Src

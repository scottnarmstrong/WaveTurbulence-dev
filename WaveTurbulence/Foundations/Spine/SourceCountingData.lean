/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDef
/-! Literal fixed choices in the spliced counting problem, TARGET L2097–L2116. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Set Finset
variable {w d : ℕ}

def IsDyadicScale (Q : ℝ) : Prop := ∃ z : ℤ, Q = (2 : ℝ) ^ z

noncomputable def atomGapKind (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (v : GBranch G.tree) : Molecule.GapKind := by
  classical
  exact if ∃ x y, TripleAt G v x y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG then .SG else
    if ∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0 then .ZG else .LG

/-- Fixed combinatorial and dyadic choices in requirements (b)–(f). Restriction centers,
energy intervals and charges are already maximized in the literal Molecule.countE. -/
structure CountingChoices (G : Garden w) (d : ℕ) where
  subpro : SubproChoices G
  secondCollection : Set (Object G.molecule)
  omittedDVConstituents : Set (Finset (GBranch G.tree))
  atomLabel : GBranch G.tree → Molecule.GapKind
  first : GBranch G.tree → Option (GardenDart G)
  second : GBranch G.tree → Option (GardenDart G)
  atomScale : GBranch G.tree → ℝ
  ladderScale : Finset (GBranch G.tree) → ℝ
  fixedRoots : Finset (Mom d)

def CountingChoices.CriticalSG {G : Garden w} (C : CountingChoices G d) (v : GBranch G.tree) : Prop :=
  C.atomLabel v = .SG ∧
    (∀ i, ¬ (C.subpro.collection i).IsInterior v) ∧
    ∀ P ∈ C.secondCollection, ¬ P.IsInterior v

noncomputable def CountingChoices.numCriticalSG {G : Garden w} (C : CountingChoices G d) : ℕ := by
  classical
  exact ((univ : Finset (GBranch G.tree)).filter C.CriticalSG).card

/-- TARGET L2101–L2112 (R6(b)): the second collection is built outside the first collection
and the hinges. The forbidden atoms of the restricted carrier. -/
def SubproChoices.forbidden {G : Garden w} (C : SubproChoices G) : Set (GBranch G.tree) :=
  ↑C.hinges ∪ ⋃ i, (↑(C.collection i).atoms : Set (GBranch G.tree))

/-- R6(a),(b): the second collection of the counting problem is the canonical part (one
designation per atom set, least deleted bond for an injective rank) of the restricted literal
collection of TARGET L2101–L2112. -/
def CountingChoices.SecondCollectionOK {G : Garden w} (C : CountingChoices G d) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∃ rk : GardenDart G → ℕ, Function.Injective rk ∧ ∃ K : Set (Object G.molecule),
    IsSourceSecondCollection G L γ η base κ C.subpro.forbidden C.omittedDVConstituents K ∧
    C.secondCollection = canonicalSub rk K

/-- Requirement (c): dyadic gap scales of every actual maximal ladder. -/
def CountingChoices.LadderGaps {G : Garden w} (C : CountingChoices G d) (L _γ _η : ℝ)
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

/-- Structural consequences and fixed choices in requirements (b)–(f). The actual epsilon/gap
support is added explicitly by splicedCountingAdmissible in SourceFinalCountInputs.
Requirement (a) is the explicit restriction inside Molecule.countE. -/
def CountingChoices.Admissible {G : Garden w} (C : CountingChoices G d) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  SubproSupport G C.subpro L γ η base C.fixedRoots κ ∧
  C.SecondCollectionOK L γ η base κ ∧
  (∀ v, atomGapKind G L γ η base κ v = C.atomLabel v) ∧
  (∀ v, C.atomLabel v = .SG → HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)) ∧
  (∀ v ∈ C.subpro.hinges, C.first v = C.subpro.first v ∧ C.second v = C.subpro.second v) ∧
  (∀ i v, (v = (C.subpro.collection i).upper ∨ v = (C.subpro.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      (C.subpro.collection i).ContainsDart x ∧ (C.subpro.collection i).ContainsDart y)) ∧
  (∀ P ∈ C.secondCollection, ∀ v, (v = P.upper ∨ v = P.lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
  (∀ v, C.CriticalSG v → IsDyadicScale (C.atomScale v) ∧
    L⁻¹ ≤ C.atomScale v ∧ C.atomScale v ≤ L ^ (-γ + η) ∧
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      C.atomScale v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧
        ‖Molecule.gapAt L base κ x y‖ ≤ 2 * C.atomScale v)) ∧
  C.LadderGaps L γ η base κ

/-- Source geometric typing: subpro(1),(2), and the explicit hinge assertion immediately
after finalcount1 (TARGET L2116). The stage-one producer must supply these source facts. -/
structure CountingGeometry {R : ℕ} (G : Garden (2 * R)) (C : CountingChoices G d) : Prop where
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

/-- The source q_sk ≤ p_sb assertion is an actual finite-cardinality consequence of the
recorded hinge facts, not an assumed numerical inequality. -/
theorem CountingGeometry.hinges_card_le {R : ℕ} {G : Garden (2 * R)} {C : CountingChoices G d}
    (h : CountingGeometry G C) : C.subpro.hinges.card ≤ C.numCriticalSG := by
  classical
  change C.subpro.hinges.card ≤ ((univ : Finset (GBranch G.tree)).filter C.CriticalSG).card
  apply Finset.card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, h.hingeSmall v hv,
    h.hingeOutsideFirst v hv, h.hingeOutsideSecond v hv⟩

end WaveTurbulence.LGSpine.SourceVine

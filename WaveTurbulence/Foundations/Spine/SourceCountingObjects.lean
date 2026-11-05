/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
/-! Explicit object selection in TARGET L2101–L2104: maximal SG objects inside DV/LG/ZG
containers, with one constituent omitted when both type-V constituents of a DV are SG. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Set Finset
variable {w d : ℕ}

noncomputable def Object.ofVine {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b : V} {X : VineType}
    (h : M.IsVine X S a b) : Object M :=
  ⟨S, a, b, .vc ⟨h.1, 1, Chain.single ⟨X, h⟩⟩⟩

/-- The actual two constituent type-V vines of a double vine. -/
structure DoubleVine (G : Garden w) where
  first : Finset (GBranch G.tree)
  second : Finset (GBranch G.tree)
  upper : GBranch G.tree
  lower : GBranch G.tree
  first_vine : G.molecule.IsVine .V first upper lower
  second_vine : G.molecule.IsVine .V second upper lower
  overlap : first ∩ second = {upper, lower}

/-- AMEND5 (R42(2)): ATOM-LEVEL eligibility (R28: TARGET's "subset" is atom sets). The container `Q` of an
LG/ZG vine-like object only has to contain the atoms of `P`; designation-level containment
(`Object.IsContained`) is not required, so a hyper SG object whose only LG/ZG hosts have the same atoms and a
different designation is eligible. It is equivalent to `literalSecondCandidate` (SourceRestrictedCarrier). -/
def eligibleSecondObject (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (P : Object G.molecule) : Prop :=
  P.HasGapKind L γ η base κ .SG ∧
    ((∃ Q : Object G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint (↑Q.atoms : Set (GBranch G.tree)) F) ∨
      ∃ D : DoubleVine G, P.atoms ⊆ D.first ∪ D.second ∧
        Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F)

/-- Literal selection rule at TARGET L2101–L2104. The omission is an atom set, so it is
independent of joint orientation and proof witnesses. Different designated hyper-objects
remain different objects through Object.IsContained, as in the VINES interface. -/
def IsSourceSecondCollection (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (Object G.molecule)) : Prop :=
  (∀ S ∈ omitted, ∃ D : DoubleVine G,
    Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F ∧
    (Object.ofVine D.first_vine).HasGapKind L γ η base κ .SG ∧
    (Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG ∧
      (S = D.first ∨ S = D.second)) ∧
  (∀ D : DoubleVine G, Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F →
    (Object.ofVine D.first_vine).HasGapKind L γ η base κ .SG →
    (Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG →
      Xor (D.first ∈ omitted) (D.second ∈ omitted)) ∧
  ∀ P : Object G.molecule, P ∈ collection ↔
    eligibleSecondObject G L γ η base κ F P ∧ P.atoms ∉ omitted ∧
      ∀ Q : Object G.molecule, eligibleSecondObject G L γ η base κ F Q → Q.atoms ∉ omitted →
        P.IsContained Q → Q.IsContained P

theorem disjointF_of_subset {α : Type*} {A B : Finset α} {F : Set α} (h : A ⊆ B)
    (hB : Disjoint (↑B : Set α) F) : Disjoint (↑A : Set α) F :=
  Set.disjoint_of_subset_left (Finset.coe_subset.mpr h) hB

theorem disjointF_union {α : Type*} [DecidableEq α] {A B : Finset α} {F : Set α}
    (hA : Disjoint (↑A : Set α) F) (hB : Disjoint (↑B : Set α) F) :
    Disjoint (↑(A ∪ B) : Set α) F := by
  rw [Finset.coe_union]; exact Set.disjoint_union_left.mpr ⟨hA, hB⟩

/-- Interior atoms exclude both actual joints, regardless of the selected orientation. -/
def Object.IsInterior {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (P : Object M) (v : V) : Prop :=
  v ∈ P.atoms ∧ v ≠ P.upper ∧ v ≠ P.lower

end WaveTurbulence.LGSpine.SourceVine

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of sp-src/SubproSupportA.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContained2R83
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItems2R83
import Mathlib.Tactic

/-!
# SUBPRO (S4): the atom-set form of `SubproSupport` (R28) and the decoration data of `G_sb`

`SubproSupportA` is `SourceVine.SubproSupport` with `Outside` / `IsContained` replaced by atom-set containment
(TARGET L2040-L2051 says "subset"; R28 ruling 3).  `sbDec_of_gen`: a generic decoration of the plain garden `G_sb`
gives the decoration data `SbDec` used by the gap-kind transport.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

/-- TARGET subpro(2)-(6) with atom-set containment (`C.Outside` becomes `∀ i, ¬ P.atoms ⊆ (C.collection i).atoms`). -/
structure SubproSupportA {w d : ℕ} (G : Garden w) (C : SubproChoices G) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) →
      G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → Disjoint P.atoms C.hinges →
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
    P.HasGapKind L γ η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

variable {R : ℕ} {G : Garden (2 * R)}

/-- B1b (Mk-general form of `sbDec_of_gen`). -/
theorem sbDec_of_genMk (σ : Prescription G) {d : ℕ} {Mk : Set (Stage1.CLVine _)} (hpl : (stSt (Mk := Mk) G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt (Mk := Mk) G σ).G d roots 0) :
    SbDec G σ L base (bondIndex (stSt (Mk := Mk) G σ).G z.1) :=
  ⟨_, spliced_molecule_decoration (stSt (Mk := Mk) G σ).G hpl hL base roots z,
    fun _ _ hdeg => gardenSource_eq_zero_of_deg_four _ hpl _ _ hdeg⟩

theorem sbDec_of_gen (σ : Prescription G) {d : ℕ} (hpl : (stSt G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt G σ).G d roots 0) :
    SbDec G σ L base (bondIndex (stSt G σ).G z.1) := sbDec_of_genMk (Mk := ∅) σ hpl hL base roots z

theorem contained_support (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ).G D L γ η base z ≠ 0) :
    ∀ P : Object (stSt G σ).G.molecule,
      P.HasGapKind L γ η base (bondIndex (stSt G σ).G z) .SG →
      (∀ i, ¬ P.atoms ⊆ ((collectionChoices G σ).collection i).atoms) →
      Disjoint P.atoms (collectionChoices G σ).hinges →
      (∃ S a b, IsDV (stSt G σ).G.molecule S a b ∧ P.atoms ⊆ S ∧
        Disjoint S (collectionChoices G σ).hinges ∧
          ∀ i, Disjoint S ((collectionChoices G σ).collection i).atoms) ∨
      ∃ Q : Object (stSt G σ).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ η base (bondIndex (stSt G σ).G z) .LG ∨
          Q.HasGapKind L γ η base (bondIndex (stSt G σ).G z) .ZG) ∧
        Disjoint Q.atoms (collectionChoices G σ).hinges ∧
          ∀ i, Disjoint Q.atoms ((collectionChoices G σ).collection i).atoms := by
  intro P _ hout hdis
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hout' : ∀ O ∈ objects G σ, ¬ P.atoms ⊆ O.atoms := by
    intro O hO
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
    have := hout i
    simp only [collectionChoices] at this
    rw [hi] at this
    exact this
  have key := contained_atoms hM σ D hD L γ η base z hZ P hout' hdis
  have hobj : ∀ S : Finset (GBranch (stSt G σ).G.tree), (∀ O ∈ objects G σ, Disjoint S O.atoms) →
      ∀ i, Disjoint S ((collectionChoices G σ).collection i).atoms := fun S h i => h _ (List.get_mem _ _)
  rcases key with ⟨S, a, b, h1, h2, h3, h4⟩ | ⟨Q, h1, h2, h3, h4⟩
  · exact Or.inl ⟨S, a, b, h1, h2, h3, hobj S h4⟩
  · exact Or.inr ⟨Q, h1, h2, h3, hobj Q.atoms h4⟩

end WaveTurbulence.VineA.NormalizedSplice.Subpro

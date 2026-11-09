/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOrdinaryJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceAtomKindAtJoints
/-! Simultaneous source pair choices for the actual disjoint primary collection and hinges. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourcePrimaryPairChoices` (sha256 6ae5a9d906a9edcafcf0c6a91dd3fbbc90829e6ba1e7d1d1b57701793d491c7b) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

private theorem object_joint_mem {w : ℕ} (G : Garden w) (P : Object γv G.molecule)
    {v : GBranch G.tree} (hv : v = P.upper ∨ v = P.lower) : v ∈ P.atoms := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h =>
    rcases hv with rfl | rfl
    · exact h.1.2.1
    · exact h.1.2.2.1
  | hyper R =>
    rcases hv with rfl | rfl
    · exact R.adjoint.1.2.1
    · exact R.adjoint.1.2.2.1

/-- Requirements (b),(d),(e) for C1 and hinges, before adjoining the secondary collection.
This consumes the literal subpro support and disjointness, not an extra spine input. -/
theorem source_primary_pair_choices {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : SubproChoices γv G) (hC : C.Structural)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (kFix : Finset (Mom d))
    (hs : SubproSupport γv G C L γ η base kFix (bondIndex G z.1)) :
    ∃ first second : GBranch G.tree → Option (GardenDart G),
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (first v) (second v) (fun x y => TripleAt G v x y ∧
          Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, first v = C.first v ∧ second v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (first v) (second v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) := by
  classical
  let SG := fun v x y => TripleAt G v x y ∧
    Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG
  let Joint := fun v i => v = (C.collection i).upper ∨ v = (C.collection i).lower
  have hjunique : ∀ v i j, Joint v i → Joint v j → i = j := by
    intro v i j hi hj
    by_contra hne
    exact Finset.disjoint_left.mp (hC.2.1 i j hne)
      (object_joint_mem G _ hi) (object_joint_mem G _ hj)
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (SG v)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, Joint v i → HasChosenPair a b (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) := by
    intro v
    by_cases hh : v ∈ C.hinges
    · exact ⟨C.first v, C.second v, fun _ => hs.hingeSG v hh, fun _ => ⟨rfl, rfl⟩,
        fun i hi => hs.hingeJoint v hh i hi⟩
    · by_cases hj : ∃ i, Joint v i
      · obtain ⟨i, hi⟩ := hj
        obtain ⟨x, y, hxy, hx, hy, hsg⟩ := source_actual_object_joint_sg_pair G hp hM
          (C.collection i) hL γ η base roots z (hs.selectedSG i) v hi
        refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy, hsg⟩,
          fun hv => False.elim (hh hv), ?_⟩
        intro j hj
        have he := hjunique v i j hi hj
        subst j
        exact ⟨x, y, rfl, rfl, hx, hy⟩
      · by_cases hsg : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
        · obtain ⟨x, y, hxy⟩ := (source_atomGapKind_eq_SG_iff G L γ η base _ v).mp hsg
          exact ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy⟩,
            fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩)⟩
        · exact ⟨none, none, fun hv => False.elim (hsg hv),
            fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩)⟩
  choose first second hsg hhinge hfirst using hlocal
  exact ⟨first, second, hsg, hhinge, fun i v hv => hfirst v i hv⟩

end WaveTurbulence.GammaLow.Famc

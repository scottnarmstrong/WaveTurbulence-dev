/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOrdinaryJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceObjectJointPairs
/-! A joint of an actual SG source object is an SG atom in the literal counting definition. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceAtomKindAtJoints` (sha256 6e4945142b2db0241774b51d4a3e27de32faed2fcb1a641efbed877a8b9154db) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}


theorem source_atomGapKind_eq_SG_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (v : GBranch G.tree) :
    atomGapKind G L γ η base κ v = .SG ↔
      ∃ x y, TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG := by
  classical
  by_cases h : ∃ x y, TripleAt G v x y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG
  · constructor
    · intro _
      exact h
    · intro _
      unfold atomGapKind
      rw [if_pos h]
  · constructor
    · intro he
      unfold atomGapKind at he
      rw [if_neg h] at he
      split_ifs at he <;> cases he
    · intro he
      exact False.elim (h he)

theorem source_actual_object_joint_is_SG {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (P : Object γv G.molecule) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hP : P.HasGapKind L γ η base (bondIndex G z.1) .SG)
    (v : GBranch G.tree) (hv : v = P.upper ∨ v = P.lower) :
    atomGapKind G L γ η base (bondIndex G z.1) v = .SG := by
  obtain ⟨x, y, hxy, _, _, hsg⟩ := source_actual_object_joint_sg_pair G hp hM P hL γ η base roots z hP v hv
  exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy, hsg⟩

end WaveTurbulence.GammaLow.Famc

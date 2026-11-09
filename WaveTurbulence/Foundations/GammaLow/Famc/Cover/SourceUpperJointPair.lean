/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Molecule.VineGapKinds
/-! Literal SG pair selection at an object's upper joint, including its designated hyper adjoint. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceUpperJointPair` (sha256 5de30c39e07eceeb7eb874b3b5aff8f139825da97cb73ec8077550d0b1b13d3a) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}


theorem source_upper_joint_sg_pair {w d : ℕ} (G : Garden w) (P : Object γv G.molecule)
    (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : ∀ x, κ (G.molecule.mate x) = κ x)
    (hP : P.HasGapKind L γ η base κ .SG) :
    ∃ x y, TripleAt G P.upper x y ∧ P.ContainsDart x ∧ P.ContainsDart y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG := by
  rcases P with ⟨S, a, b, shape⟩
  rcases hP with ⟨r, hr, hkind⟩
  have hr0 := ((Vine.gapKind_eq_SG_iff L γ η r).mp hkind).1
  cases shape with
  | vc hVC =>
    obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr
    have hne : y ≠ G.molecule.mate x := by
      intro he
      apply hr0
      rw [hgap, he]
      simp only [Molecule.gapAt, Molecule.kvec, hκ, sub_self]
    refine ⟨x, y, ⟨hx, hy, hne, ?_⟩, hgx, hgy, ?_⟩
    · rw [hox, hoy]
      decide
    · simpa only [hgap] using hkind
  | hyper R =>
    obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr
    have hgap' : r = Molecule.gapAt L base κ x.1 y.1 := hgap
    have hne : y.1 ≠ G.molecule.mate x.1 := by
      intro he
      apply hr0
      rw [hgap', he]
      simp only [Molecule.gapAt, Molecule.kvec, hκ, sub_self]
    refine ⟨x.1, y.1, ⟨hx, hy, hne, ?_⟩, ⟨x.2.1, x.2.2, hgx⟩, ⟨y.2.1, y.2.2, hgy⟩, ?_⟩
    · change G.molecule.out x.1 ≠ G.molecule.out y.1
      change G.molecule.out x.1 = true at hox
      change G.molecule.out y.1 = false at hoy
      rw [hox, hoy]
      decide
    · simpa only [hgap'] using hkind

end WaveTurbulence.GammaLow.Famc

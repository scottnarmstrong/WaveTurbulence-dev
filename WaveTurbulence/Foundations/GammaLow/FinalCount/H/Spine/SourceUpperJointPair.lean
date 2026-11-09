/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceUpperJointPair`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal SG pair selection at an object's upper joint, including its designated hyper adjoint. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine

theorem source_upper_joint_sg_pair {w d : ℕ} (G : Garden w) (P : Src.Object Src.γL G.molecule)
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
    · change G.molecule.out x.1 = true at hox
      change G.molecule.out y.1 = false at hoy
      rw [hox, hoy]
      decide
    · simpa only [hgap'] using hkind

end WaveTurbulence.GammaLow.FinalCount.H

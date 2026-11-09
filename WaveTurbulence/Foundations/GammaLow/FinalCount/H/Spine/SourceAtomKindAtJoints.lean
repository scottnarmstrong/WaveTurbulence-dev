/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceAtomKindAtJoints`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 A joint of an actual SG source object is an SG atom in the literal counting definition. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine

theorem source_actual_object_joint_is_SG {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (P : Src.Object Src.γL G.molecule) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hP : P.HasGapKind L γ η base (bondIndex G z.1) .SG)
    (v : GBranch G.tree) (hv : v = P.upper ∨ v = P.lower) :
    atomGapKind G L γ η base (bondIndex G z.1) v = .SG := by
  obtain ⟨x, y, hxy, _, _, hsg⟩ := source_actual_object_joint_sg_pair G hp hM P hL γ η base roots z hP v hv
  exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy, hsg⟩

end WaveTurbulence.GammaLow.FinalCount.H

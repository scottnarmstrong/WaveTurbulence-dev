/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomScaleExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceLadderGapExists
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceLadderGapExists
public import WaveTurbulence.Foundations.Spine.SourceAtomScaleExists
/-! Requirements (c),(f) are constructed from the actual source's combinatorial pair choices. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
-- Ported from main `Spine.SourceCountingChoiceScales` (sha256 01feaaf59f7f5459b61f5da4229df8744f3027d910048404e6af5d1169889ca0) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}

/-- Once requirements (b),(d),(e) hold on the actual momentum labels, both sets of dyadic
scales can be supplied. This is an assembly helper, not an additional spine input. -/
theorem exists_admissible_scales_of_pair_choices {w d : ℕ} (G : Garden w)
    (C : CountingChoices γv G d) {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ)
    (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ))
    (hsub : SubproSupport γv G C.subpro L γ η base C.fixedRoots κ)
    (hcollection : C.SecondCollectionOK L γ η base κ)
    (hlabel : ∀ v, SourceVine.atomGapKind G L γ η base κ v = C.atomLabel v)
    (hsg : ∀ v, C.atomLabel v = .SG → SourceVine.HasChosenPair (C.first v) (C.second v)
      (fun x y => SourceVine.TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG))
    (hhinge : ∀ v ∈ C.subpro.hinges, C.first v = C.subpro.first v ∧ C.second v = C.subpro.second v)
    (hfirst : ∀ i v, (v = (C.subpro.collection i).upper ∨ v = (C.subpro.collection i).lower) →
      SourceVine.HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.subpro.collection i).ContainsDart x ∧ (C.subpro.collection i).ContainsDart y))
    (hsecond : ∀ P ∈ C.secondCollection, ∀ v, (v = P.upper ∨ v = P.lower) →
      SourceVine.HasChosenPair (C.first v) (C.second v) (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) :
    ∃ atomScale ladderScale,
      ({C with atomScale := atomScale, ladderScale := ladderScale}).Admissible L γ η base κ := by
  have hL0 : 0 < L := by linarith
  obtain ⟨atomScale, hatom⟩ := exists_counting_atomScales G C hL0 γ η hcap base κ (by
    intro v hv
    obtain ⟨x, y, hx, hy, _, hgap⟩ := hsg v hv
    exact ⟨x, y, hx, hy, hgap⟩)
  obtain ⟨ladderScale, hladder⟩ := exists_counting_ladderScales G C hL γ η base κ
  refine ⟨atomScale, ladderScale, hsub, hcollection, hlabel, hsg, hhinge, hfirst, hsecond, ?_, ?_⟩
  · intro v hv
    exact hatom v hv
  · exact hladder

end WaveTurbulence.GammaLow.Famc

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverTags
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! Every surviving decoration of the spliced kernel is admissible for a finite tagged choice
(TARGET L2097-L2116), over arbitrary subpro choice data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.Cover
open WaveTurbulence.Induct
open SourceVine Set Finset WaveTurbulence.LGSpine
open scoped Classical

variable {d : ℕ}

/-- The decorated conclusions of TARGET subpro (L2040-L2051) for given choice data `Cs`, in the
form of `SplicedSourcePremises.subpro` (fixed roots = the root momenta), together with the
C1 half of the hinge assertion at L2116. Hypotheses of the conditional helpers
`*_of_subpro_choices`; the construction of `Cs` is S2a, `subpro` is S4. -/
structure SubproConclusions {R : ℕ} (G : Garden (2 * R)) (D : SplicedKernelData G d)
    (Cs : SubproChoices G) (L γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) : Prop where
  structural : Cs.Structural
  hinges : D.hinges = Cs.hinges
  support : ∀ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D L γ η base z.1 ≠ 0 →
    SubproSupport G Cs L γ η base (univ.image (fun i => base + latticePoint L (roots i)))
      (bondIndex G z.1)
  /-- TARGET L2116, C1 half: no hinge is an interior atom of an object of `C_1`. -/
  hingeOutsideFirst : ∀ v ∈ Cs.hinges, ∀ i, ¬ (Cs.collection i).IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : Cs.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : Cs.HingeNoLoop

theorem exists_cover_choice_of_subpro_choices {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (Cs : SubproChoices G) {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ)
    (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ))
    (hS : SubproConclusions G D Cs L γ η base roots)
    (z : GenDecoration G d roots 0) (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0) :
    ∃ (t : Tag G) (s : Scales (tagChoice G hM Cs L γ η base roots t) L γ η),
      (fullChoice (tagChoice G hM Cs L γ η base roots t) s).Admissible L γ η base
        (bondIndex G z.1) := by
  have hL0 : L ≠ 0 := by linarith
  obtain ⟨he, hg, _⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  have hsup := hS.support z he hg
  obtain ⟨τ, hτ⟩ : ∃ τ, sourceGapTable G L γ η base (bondIndex G z.1) = τ := ⟨_, rfl⟩
  have hK := secondOf_spec G hM L γ η base Cs.forbidden τ (bondIndex G z.1) hτ
  have hK' : IsSourceSecondCollection G L γ η base (bondIndex G z.1) Cs.forbidden
      (secondOf G hM L γ η base Cs.forbidden τ).1 (secondOf G hM L γ η base Cs.forbidden τ).2 := hK
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := source_full_pair_table G hp hM Cs hS.structural hL0 γ η base
    roots z _ hsup hK' (dartRank G) (dartRank_injective G)
  have hlabel : ∀ v, atomGapKind G L γ η base (bondIndex G z.1) v =
      (tagChoice G hM Cs L γ η base roots (τ, T)).atomLabel v := by
    intro v
    rw [tagChoice_atomLabel]
    have h1 : sourceGapTable G L γ η base (bondIndex G z.1) =
        sourceGapTable G L γ η base (kappaOf G L γ η base τ) :=
      hτ.trans (kappaOf_table G L γ η base τ (bondIndex G z.1) hτ).symm
    exact sourceGapTable_atomGapKind_eq G L γ η base (bondIndex G z.1) _ h1 v
  obtain ⟨as, ls, hadm⟩ := exists_admissible_scales_of_pair_choices G
    (tagChoice G hM Cs L γ η base roots (τ, T)) hL γ η hcap base (bondIndex G z.1)
    hsup ⟨dartRank G, dartRank_injective G, _, hK', rfl⟩ hlabel
    (by intro v hv; exact hT1 v ((hlabel v).trans hv))
    hT2 hT3 hT4
  obtain ⟨s, hs⟩ := exists_scales_of_admissible _ base (bondIndex G z.1) as ls hadm
  exact ⟨(τ, T), s, hs⟩

end WaveTurbulence.LGSpine.Cover

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLadderGapExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceLadderGapExists`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Every actual source ladder has a first-rail gap and an admissible dyadic scale. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Finset

/-- All actual maximal ladders can be assigned scales simultaneously, independently
of the other fixed counting choices. No uniform gap-existence hypothesis is assumed. -/
theorem exists_counting_ladderScales {w d : ℕ} (G : Garden w)
    (C : Src.CountingChoices Src.γL G d) {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) :
    ∃ scale : Finset (GBranch G.tree) → ℝ,
      ({C with ladderScale := scale}).LadderGaps L γ η base κ := by
  classical
  obtain ⟨A⟩ := sourceMaximalLadderData_nonempty G
  have hex (S : {S // S ∈ G.molecule.maximalLadders}) :=
    exists_sourceLadderGap G.molecule L base κ (A.upper S) (A.lower S) (A.ladder S)
  choose r hr using hex
  have hp (S : {S // S ∈ G.molecule.maximalLadders}) :=
    exists_ladder_gap_scale G.molecule hL base κ (A.upper S) (A.lower S) (A.ladder S).1 (r S) (hr S)
  choose P hP using hp
  let scale (S : Finset (GBranch G.tree)) : ℝ := if h : S ∈ G.molecule.maximalLadders then P ⟨S,h⟩ else 0
  refine ⟨scale, ?_⟩
  intro S hS
  have he : scale S = P ⟨S,hS⟩ := by simp only [scale, dite_eq_left hS]
  dsimp only
  rw [he]
  exact ⟨(hP ⟨S,hS⟩).1, A.length ⟨S,hS⟩, A.upper ⟨S,hS⟩, A.lower ⟨S,hS⟩,
    (A.ladder ⟨S,hS⟩).1, A.ladder ⟨S,hS⟩, A.atoms ⟨S,hS⟩, r ⟨S,hS⟩,
      hr ⟨S,hS⟩, (hP ⟨S,hS⟩).2⟩

end WaveTurbulence.GammaLow.FinalCount.H

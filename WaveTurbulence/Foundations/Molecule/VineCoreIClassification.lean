/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned I core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-I block degree masks occur in the finite table. -/
theorem coreI_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .I 2 mask a b) :
    coreMaskVector .I mask ∈ coreMaskCandidates .I .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<2 at hbn
  have han : a<2 := hab.trans hbn
  interval_cases a
  · have hh := coreI_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_I_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_I_1] using hdegree 1 (by decide))
    have hs : ∀ v ∈ ([[1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .I .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-I hyper degree masks occur in the finite table. -/
theorem coreI_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .I 3 mask a b) :
    coreMaskVector .I mask ∈ coreMaskCandidates .I .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<2 at hbn
  have han : a<2 := hab.trans hbn
  interval_cases a
  · have hh := coreI_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_I_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_I_1] using hdegree 1 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .I .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

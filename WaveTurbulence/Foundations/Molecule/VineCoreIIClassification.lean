/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreIIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned II core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-II block degree masks occur in the finite table. -/
theorem coreII_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .II 2 mask a b) :
    coreMaskVector .II mask ∈ coreMaskCandidates .II .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<4 at hbn
  have han : a<4 := hab.trans hbn
  interval_cases a
  · have hh := coreII_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .II .block := by decide
    exact hs _ hh
  · have hh := coreII_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .II .block := by decide
    exact hs _ hh
  · have hh := coreII_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .II .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-II hyper degree masks occur in the finite table. -/
theorem coreII_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .II 3 mask a b) :
    coreMaskVector .II mask ∈ coreMaskCandidates .II .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<4 at hbn
  have han : a<4 := hab.trans hbn
  interval_cases a
  · have hh := coreII_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .II .hyper := by decide
    exact hs _ hh
  · have hh := coreII_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .II .hyper := by decide
    exact hs _ hh
  · have hh := coreII_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_II_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_II_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_II_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_II_3] using hdegree 3 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .II .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

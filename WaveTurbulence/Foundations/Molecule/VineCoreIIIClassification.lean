/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIIIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreIIIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned III core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-III block degree masks occur in the finite table. -/
theorem coreIII_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .III 2 mask a b) :
    coreMaskVector .III mask ∈ coreMaskCandidates .III .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<9 at hbn
  have han : a<9 := hab.trans hbn
  interval_cases a
  · have hh := coreIII_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,1,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · have hh := coreIII_block_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .III .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-III hyper degree masks occur in the finite table. -/
theorem coreIII_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .III 3 mask a b) :
    coreMaskVector .III mask ∈ coreMaskCandidates .III .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<9 at hbn
  have han : a<9 := hab.trans hbn
  interval_cases a
  · have hh := coreIII_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · have hh := coreIII_hyper_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_III_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_III_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_III_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_III_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_III_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_III_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_III_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_III_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_III_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .III .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVIIIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned VIII core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-VIII block degree masks occur in the finite table. -/
theorem coreVIII_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VIII 2 mask a b) :
    coreMaskVector .VIII mask ∈ coreMaskCandidates .VIII .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<11 at hbn
  have han : a<11 := hab.trans hbn
  interval_cases a
  · have hh := coreVIII_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,0,0,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,1,1,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,1,0,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · have hh := coreVIII_block_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-VIII hyper degree masks occur in the finite table. -/
theorem coreVIII_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VIII 3 mask a b) :
    coreMaskVector .VIII mask ∈ coreMaskCandidates .VIII .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<11 at hbn
  have han : a<11 := hab.trans hbn
  interval_cases a
  · have hh := coreVIII_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · have hh := coreVIII_hyper_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VIII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VIII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VIII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VIII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VIII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VIII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VIII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VIII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VIII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VIII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VIII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VIII .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

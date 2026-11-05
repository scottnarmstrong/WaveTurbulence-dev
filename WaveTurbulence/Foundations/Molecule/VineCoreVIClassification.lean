/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned VI core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-VI block degree masks occur in the finite table. -/
theorem coreVI_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VI 2 mask a b) :
    coreMaskVector .VI mask ∈ coreMaskCandidates .VI .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<15 at hbn
  have han : a<15 := hab.trans hbn
  interval_cases a
  · have hh := coreVI_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,0,0,0,0,0,0,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,0,0,0,0,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,1,1,0,0,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,1,1,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_10 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,0,1,0,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_11 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,0,0,1,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_12 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · have hh := coreVI_block_13 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,0,0,0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-VI hyper degree masks occur in the finite table. -/
theorem coreVI_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VI 3 mask a b) :
    coreMaskVector .VI mask ∈ coreMaskCandidates .VI .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<15 at hbn
  have han : a<15 := hab.trans hbn
  interval_cases a
  · have hh := coreVI_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,1,1,1,1,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_10 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,0,1,1,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_11 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_12 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · have hh := coreVI_hyper_13 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VI_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VI_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VI_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VI_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VI_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VI_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VI_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VI_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VI_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VI_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VI_10] using hdegree 10 (by decide))
        (by simpa only [coreDegree_VI_11] using hdegree 11 (by decide))
        (by simpa only [coreDegree_VI_12] using hdegree 12 (by decide))
        (by simpa only [coreDegree_VI_13] using hdegree 13 (by decide))
        (by simpa only [coreDegree_VI_14] using hdegree 14 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VI .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

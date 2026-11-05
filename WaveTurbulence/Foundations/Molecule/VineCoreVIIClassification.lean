/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVIIBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned VII core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-VII block degree masks occur in the finite table. -/
theorem coreVII_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VII 2 mask a b) :
    coreMaskVector .VII mask ∈ coreMaskCandidates .VII .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<11 at hbn
  have han : a<11 := hab.trans hbn
  interval_cases a
  · have hh := coreVII_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,0,0,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,0,1,0,0,0,0],[0,0,0,0,1,1,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,1,1,1,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · have hh := coreVII_block_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-VII hyper degree masks occur in the finite table. -/
theorem coreVII_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .VII 3 mask a b) :
    coreMaskVector .VII mask ∈ coreMaskCandidates .VII .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<11 at hbn
  have han : a<11 := hab.trans hbn
  interval_cases a
  · have hh := coreVII_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,1,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_8 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · have hh := coreVII_hyper_9 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_VII_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_VII_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_VII_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_VII_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_VII_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_VII_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_VII_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_VII_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_VII_8] using hdegree 8 (by decide))
        (by simpa only [coreDegree_VII_9] using hdegree 9 (by decide))
        (by simpa only [coreDegree_VII_10] using hdegree 10 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .VII .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

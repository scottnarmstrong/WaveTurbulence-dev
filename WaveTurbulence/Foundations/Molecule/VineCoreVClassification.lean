/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVBlock
public import WaveTurbulence.Foundations.Molecule.VineCoreVHyper
public import WaveTurbulence.Foundations.Molecule.VineCoreDegrees
import Mathlib.Tactic

/-! # Complete degree-mask classification for the pinned V core -/

public section
namespace WaveTurbulence.Vine

/-- All exact type-V block degree masks occur in the finite table. -/
theorem coreV_block_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .V 2 mask a b) :
    coreMaskVector .V mask ∈ coreMaskCandidates .V .block := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<9 at hbn
  have han : a<9 := hab.trans hbn
  interval_cases a
  · have hh := coreV_block_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[1,1,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,0,0,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,0,0,0]] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,1,0,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · have hh := coreV_block_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,0,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .block := by decide
    exact hs _ hh
  · omega

/-- All exact type-V hyper degree masks occur in the finite table. -/
theorem coreV_hyper_exhaustive (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape .V 3 mask a b) :
    coreMaskVector .V mask ∈ coreMaskCandidates .V .hyper := by
  obtain ⟨hab,hbn,ha,hb,hbound,hdegree⟩ := h
  change b<9 at hbn
  have han : a<9 := hab.trans hbn
  interval_cases a
  · have hh := coreV_hyper_0 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_1 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_2 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,1,1,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_3 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_4 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,1,1,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_5 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_6 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([[0,0,0,0,0,0,1,1,1]] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · have hh := coreV_hyper_7 mask b hab hbn ha hb hbound
        (by simpa only [coreDegree_V_0] using hdegree 0 (by decide))
        (by simpa only [coreDegree_V_1] using hdegree 1 (by decide))
        (by simpa only [coreDegree_V_2] using hdegree 2 (by decide))
        (by simpa only [coreDegree_V_3] using hdegree 3 (by decide))
        (by simpa only [coreDegree_V_4] using hdegree 4 (by decide))
        (by simpa only [coreDegree_V_5] using hdegree 5 (by decide))
        (by simpa only [coreDegree_V_6] using hdegree 6 (by decide))
        (by simpa only [coreDegree_V_7] using hdegree 7 (by decide))
        (by simpa only [coreDegree_V_8] using hdegree 8 (by decide))
    have hs : ∀ v ∈ ([] : List (List ℕ)), v ∈ coreMaskCandidates .V .hyper := by decide
    exact hs _ hh
  · omega

end WaveTurbulence.Vine

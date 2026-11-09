/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceLadderInputs
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
/-! The actual nonzero spliced summands lie in the ladder input's explicit frequency carrier. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedFrequencySupport` (sha256 e8b468a9b4003183445566eecc7d1a84c6351e4eedf2f41462303bcab7c8ead0) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem sourceLadderGapScales_of_counting {w d : ℕ} {G : Garden w}
    (C : CountingChoices γv G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (h : C.LadderGaps L γ η base κ) :
    sourceLadderGapScales G C.ladderScale L base κ := h

theorem splicedFrequency_mem_spectrum {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (C : CountingChoices γv G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0)
    (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hC : C.Admissible L γ η base (bondIndex G z.1)) :
    splicedFrequency G D L γ δ base z.1 ∈
      splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots := by
  obtain ⟨hε, hZ, hballs⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  rcases hC with ⟨_, _, _, _, _, _, _, _, hgap⟩
  exact ⟨z, hε, hZ, hballs, sourceLadderGapScales_of_counting C L γ η base _ hgap, rfl⟩

theorem frequency_floor_box {w : ℕ} (G : Garden w) (A : Set (GBranch G.tree → ℝ))
    (α : GBranch G.tree → ℝ) (hα : α ∈ A) :
    (fun v => ⌊α v⌋) ∈ sourceFrequencyBoxes G A := ⟨α, hα, fun _ => rfl⟩

theorem enorm_splicedFourierB_le_box {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (A : Set (GBranch G.tree → ℝ)) (α : GBranch G.tree → ℝ) (hα : α ∈ A) :
    ‖splicedFourierB G layer rootTime α‖ₑ ≤
      ⨆ (β : GBranch G.tree → ℝ) (_ : β ∈ A) (_ : ∀ v, |β v - (⌊α v⌋ : ℤ)| ≤ 1),
        ‖splicedFourierB G layer rootTime β‖ₑ := by
  have hbox : ∀ v, |α v - (⌊α v⌋ : ℤ)| ≤ 1 := by
    intro v
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (α v)]
  exact le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le hbox le_rfl))

end WaveTurbulence.GammaLow.Famc

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFrequencyCount
public import WaveTurbulence.Foundations.Spine.SplicedFrequencySupport
public import WaveTurbulence.Foundations.Spine.CountedFrequencySum
/-! Literal fixed-choice part of the spliced kernel and its source frequency decomposition. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

/-- The nonzero summands satisfying the fixed choices (d)–(f). -/
def splicedSelectedCarrier {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (C : SourceVine.CountingChoices G d) (L γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) : Set (GenDecoration G d roots 0) :=
  {z | splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 ∧ C.Admissible L γ η base (bondIndex G z.1)}

noncomputable def splicedSelectedKernel {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (C : SourceVine.CountingChoices G d) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order *
    ∑' z : splicedSelectedCarrier G D C L γ η base roots,
      splicedMomentumAmplitude G D L γ η base z.1.1 *
        splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1.1)

/-- Every selected summand has a realized integer box in the literal ladder input. -/
noncomputable def splicedSelectedBox {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (C : SourceVine.CountingChoices G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : splicedSelectedCarrier G D C L γ η base roots) :
    sourceFrequencyBoxes G (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots) :=
  ⟨(fun v => ⌊splicedFrequency G D L γ δ base z.1.1 v⌋),
    frequency_floor_box G _ _ (splicedFrequency_mem_spectrum G D hD C L γ η δ base roots z.1 z.2.1 z.2.2)⟩

theorem splicedSelectedBox_fiber_count {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : SourceVine.CountingChoices G d)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ))
    (σ : sourceFrequencyBoxes G (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots)) :
    ((splicedSelectedBox G D hD C L γ η δ base roots ⁻¹' {σ}).encard : ℝ≥0∞) ≤
      (G.molecule.countE L γ δ base (splicedCountingAdmissible G D C L γ η base roots) : ℝ≥0∞) := by
  have hmap : Set.MapsTo (fun z : splicedSelectedCarrier G D C L γ η base roots => z.1)
      (splicedSelectedBox G D hD C L γ η δ base roots ⁻¹' {σ})
      (splicedFrequencyFiber G D C L γ η δ base roots σ.1) := by
    intro z hz
    have he : splicedSelectedBox G D hD C L γ η δ base roots z = σ := hz
    have he' := congrArg Subtype.val he
    exact ⟨z.2.1, z.2.2, fun v => congrFun he' v⟩
  have hh := Set.encard_le_encard_of_injOn hmap (fun x _ y _ he => Subtype.ext he)
  have hh' := hh.trans (encard_splicedFrequencyFiber_le_countE G hp D hD C hL hδ γ η base roots σ.1)
  exact_mod_cast hh'

end WaveTurbulence.LGSpine

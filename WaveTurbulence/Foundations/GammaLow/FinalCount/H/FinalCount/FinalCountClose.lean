/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.FinalCountClose
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain46
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopMain3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGlue
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.FinalCountClose`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-CLOSE: the unconditional final-count gate.**

`finalCount_half : FinalCountGateHalf` (main: with no hypotheses; here given `[Src.LowInputs]`): the REG half `finalCount_reg_half` (no named input),
the LOW half through the garden bound `lowGardenBoundAll_of_loopClassBound low_loop_class_bound_all'`
(LOW-GARDEN #3 and LOW-CHAIN #6) and `finalCount_half_of_lowGarden` (LOW-GLUE).  The only glue is the
reshaping of the quantifier forms (`γ ∈ Ioo (1/2) 1` and `η ∈ Ioc 0 η₀` versus the strict/weak inequalities).

**Low-range change (L6-HLOW).** Everything is at `0 < γ ≤ 1/2`: `low_loop_class_bound_all'` from LowChain46's
`low_loop_class_bound_all` (`γ ∈ Ioc 0 (1/2)`), `finalCount_low_half : WTPrefix (fun P => P.γ ≤ 1/2 → FinalCountLowAt P)`,
`finalCount_half : FinalCountGateHalf` (H-MS2's restated row 6) via `finalCount_low_of_low` (H-ASM; REG half
`finalCount_reg_low`). The single named input is the LOW layer's class `[Src.LowInputs]` (the ghost step `chainCoverL`,
RULING R194), threaded from LowChain45. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set (Ioo Ioc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

/-- `low_loop_class_bound_all` in the inequality form consumed by `lowGardenBoundAll_of_loopClassBound`. -/
theorem low_loop_class_bound_all' [Src.LowInputs] :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → LowLoopClassBound d γ η := by
  intro d hd γ h1 h2
  obtain ⟨η₀, h0, h⟩ := low_loop_class_bound_all d hd γ ⟨h1, h2⟩
  exact ⟨η₀, h0, fun η hη hη' => h η ⟨hη, hη'⟩⟩

/-- **The LOW garden bound** (LOW-GARDEN #3 from LOW-CHAIN #6), given the LOW layer's input class. -/
theorem lowGardenBoundAll [Src.LowInputs] : LowGardenBoundAll :=
  lowGardenBoundAll_of_loopClassBound low_loop_class_bound_all'

/-- **The LOW half of the amended final-count gate** (low range), given `[Src.LowInputs]`. -/
theorem finalCount_low_half [Src.LowInputs] : WTPrefix (fun P => P.γ ≤ 1 / 2 → FinalCountLowAt P) :=
  finalCount_low_half_of_garden lowGardenBoundAll

/-- **`FinalCountGateHalf`** (low range; REG: `finalCount_reg_low`; LOW: `finalCount_low_half`), given `[Src.LowInputs]`. -/
theorem finalCount_half [Src.LowInputs] : FinalCountGateHalf :=
  finalCount_low_of_low finalCount_low_half

end WaveTurbulence.GammaLow.FinalCount.H

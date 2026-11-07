/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain46
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopMain3
public import WaveTurbulence.Foundations.FinalCount.LowGlue
/-! **FINALCOUNT-CLOSE: the unconditional final-count gate.**

`finalCount_half : FinalCountGateHalf` with no hypotheses: the REG half `finalCount_reg_half` (no named input),
the LOW half through the garden bound `lowGardenBoundAll_of_loopClassBound low_loop_class_bound_all'`
(LOW-GARDEN #3 and LOW-CHAIN #6) and `finalCount_half_of_lowGarden` (LOW-GLUE).  The only glue is the
reshaping of the quantifier forms (`γ ∈ Ioo (1/2) 1` and `η ∈ Ioc 0 η₀` versus the strict/weak inequalities). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set (Ioo Ioc)
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

/-- `low_loop_class_bound_all` in the inequality form consumed by `lowGardenBoundAll_of_loopClassBound`. -/
theorem low_loop_class_bound_all' :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 1 / 2 < γ → γ < 1 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → LowLoopClassBound d γ η := by
  intro d hd γ h1 h2
  obtain ⟨η₀, h0, h⟩ := low_loop_class_bound_all d hd γ ⟨h1, h2⟩
  exact ⟨η₀, h0, fun η hη hη' => h η ⟨hη, hη'⟩⟩

/-- **The LOW garden bound, unconditionally** (LOW-GARDEN #3 from LOW-CHAIN #6). -/
theorem lowGardenBoundAll : LowGardenBoundAll :=
  lowGardenBoundAll_of_loopClassBound low_loop_class_bound_all'

/-- **The LOW half of the amended final-count gate, unconditionally.** -/
theorem finalCount_low_half : WTPrefix (fun P => 1 / 2 < P.γ → FinalCountLowAt P) :=
  finalCount_low_half_of_garden lowGardenBoundAll

/-- **`FinalCountGateHalf`, with no hypotheses** (REG: `finalCount_reg_half`; LOW: `finalCount_low_half`). -/
theorem finalCount_half : FinalCountGateHalf :=
  finalCount_half_of_low finalCount_low_half

end WaveTurbulence.FinalCountAsm

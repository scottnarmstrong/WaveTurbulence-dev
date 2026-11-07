/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.FamilyAssembly
public import WaveTurbulence.Foundations.FlowerTop.AnalyticSpine
public import WaveTurbulence.Foundations.FlowerTop.P5Coarse
public import WaveTurbulence.Foundations.FlowerTop.P5Ladder
public import WaveTurbulence.Foundations.FinalCount.FinalCountClose

/-! Final assembly of the frozen `layergardenFlower_v3` body in the frozen world.
The couple clause is P7's, with P5's witnesses and the main-world leafwise providers discharged;
the flower clauses come from FC23's family input (plain, cut1) and C2-E-B (cut2). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine

/-- The couple half of frozen v3 from P7, over the producer input `Stage1STInput` (STB2) and the final count. -/
theorem coupleHalf_of_spine (hS : Stage1STInput) (hcount : FinalCountGateHalf) : WTPrefixP CoupleHalfAt :=
  prefixP_map (couple_clause_moment_of_inputs ⟨p5CoarseInput, p5LadderInput⟩ hS hcount) fun _ _ h => h

/-- The j₂ = 0 cut2 clause of frozen D13 (owner: C2-E-B, R98). -/
abbrev Cut2ZeroFrozenInput : Prop := WTPrefixP (FlowerCaseAt CaseCut2Zero)

/-- **`layergardenFlower_v3` from its owners' inputs.** Binders, each with its owner:
`hFam` (FC23 uniform family; plain and cut1), `hCut2` (C2-E-B positive cut2), `hCut2Zero` (C2-E-B, j₂ = 0),
`hStage1` (S2-ST: the STB2 producer), `hcount` (final count). -/
theorem layergardenFlower_v3_of_owners (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p)
    (hFam : WTPrefixP (FC23UniformCut1Input C U))
    (hCut2 : Cut2EB.PositiveCut2FrozenInput)
    (hCut2Zero : Cut2ZeroFrozenInput)
    (hStage1 : Stage1STInput) (hcount : FinalCountGateHalf) : V2Chain.LayergardenFlowerV3Gate :=
  layergardenFlower_v3_of_family C U hC hU hFam (prefixP_map hCut2 fun _ _ h => cut2_of_C2EB h)
    hCut2Zero (coupleHalf_of_spine hStage1 hcount)

/-- **`layergardenFlower_v3` with exactly four binders** (R104): the final count is discharged by main's
`FinalCountAsm.finalCount_half`, and `hStage1` is the plain `LGSpine.Stage1ReductionGate`. -/
theorem layergardenFlower_v3_of_owners' (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p)
    (hFam : WTPrefixP (FC23UniformCut1Input C U))
    (hCut2 : Cut2EB.PositiveCut2FrozenInput)
    (hCut2Zero : Cut2ZeroFrozenInput)
    (hStage1 : LGSpine.Stage1ReductionGate) : V2Chain.LayergardenFlowerV3Gate :=
  layergardenFlower_v3_of_owners C U hC hU hFam hCut2 hCut2Zero hStage1
    WaveTurbulence.FinalCountAsm.finalCount_half

end WaveTurbulence.FlowerTop

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.FamilyWeightLimit
public import WaveTurbulence.Foundations.FlowerTop.FinalAssembly
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

end WaveTurbulence.FlowerTop

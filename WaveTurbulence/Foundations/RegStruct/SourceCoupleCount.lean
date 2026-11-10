/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceRegularDecoding
public import WaveTurbulence.Foundations.RegStruct.CarrierUniqueness
public import WaveTurbulence.Foundations.RegStruct.CodeCount

/-! # Exponential counting of actual source-regular couples

Every source object has well-formed data, and a fixed code determines one
carrier. Choosing such data embeds the actual source objects in the finite
code set. Injectivity of decoding in the opposite direction is not needed
for this upper bound and is not asserted here.
-/

@[expose] public section
namespace WaveTurbulence.Reg

/-- The finite set of codes of a given order. -/
theorem finite_coupleCodes (m : ℕ) : Finite {Q : RegCpl // Q.wf = true ∧ Q.size = 2*m} :=
  Finite.of_injective (fun Q => wordSlots (8*m+1) (boundedCoupleWord m Q))
    ((wordSlots_injective _).comp (boundedCoupleWord_injective m))

end WaveTurbulence.Reg

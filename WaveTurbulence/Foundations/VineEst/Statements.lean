/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.Statements

/-! # The stable V5 statement layer (batch 4b-1)

Entry module of PORT batch 4b-1: the kind-generic VINEEST statements `VineEstCanonLayerC2MK` and
`VineEstCanonLayerHalfMK` (`VineEstS5C.P4.W2.ModStatement`) with their definition closure, and the
V5-SPACE statement definitions `VineFlatC2MX`, `VineFlatHalfMX`, `VineUpperC2MX`, `VineUpperHalfMX`
(`VineSpaceK.Statements`, definitions split from the proof modules).  No proof of the VINEEST or V5-SPACE
estimates is imported here.
-/

@[expose] public section
set_option autoImplicit false
end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface

/-! # V5 FINAL interface (REPAIRED on port)

The uni-space original defined `VineSpaceK.UniformTermCertAtK` and `VineSpaceK.UniformTermCertTargetK` (bodies identical
to main's `VineEstS5C.P4.Final.Iface`). Main now has them in `VineEstS5C.P4.Final`; this module re-exports them under
the old names so that the ported modules and consumers see main's constants (the ones `W2.uniformTermCertK` proves). -/

@[expose] public section
namespace WaveTurbulence.VineSpaceK
export WaveTurbulence.VineEstS5C.P4.Final (UniformTermCertAtK UniformTermCertTargetK)
end WaveTurbulence.VineSpaceK

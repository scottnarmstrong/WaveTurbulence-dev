/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix
public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Gt

/-! # V5-KIND final: `RealityAll` from PL234 `reality_all`

`RealityAll` (P1/Mix, R46) is by definition the exact type of PL234's `reality_all` (Prop 6.3 (iii), TARGET (layerregest10)'s
realness input, `PL234Draft/P4Gt.lean`); `realityAll` discharges it.  The PL234 closure (PL234Draft P4*/Sep*/Gate61*, the MEXP J6/J7
closure up to `MexpDraft.RegCancelB2`) is compiled here in the V5 (snapshot-9) environment from pl234's sources
(COPIED-SHA256SUMS-pl234).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P1

/-- **PL234 `reality_all` discharges `RealityAll`.** -/
theorem realityAll : RealityAll := @WaveTurbulence.PL234.reality_all

end WaveTurbulence.VineEstS5C.P1

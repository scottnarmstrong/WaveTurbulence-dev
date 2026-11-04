/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegChain.JBtree

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref2-2); T L1185–L1188; T Def `defkg`, L682–L684. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **`𝒥ℬ*_𝒯(t, s)`** of a dominant tree code (T (regref2-2)): `∫_{t > t₁ > ⋯ > t_{m₀} > max(s, r)}
∏_j ∏_ι 𝒥ℬ*_{𝒬_{j,0,ι}}(t_j, t_j) dt`. T states (regref2-2) for `s ∈ [r, r+1]` (T L1185–L1188). For `s < r`
(the lone leaf in a lower layer `q' < r`: the box of B2.1 items (2) and (3)), the constraint `t_{m₀} > s` of the
kernel `K*_𝒯` (T Def `defkg`, L682–L684) is implied by `t_{m₀} > r`, so the lower limit is `r` (B2-CL-13, FINDINGS
F66: with lower limit `s`, items (2) and (3) were false for `q' < r`). -/
noncomputable def RegChain.JBtree (r : ℝ) (X : RegChain) (t s : ℝ) : ℝ := X.JBchain r (max s r) t fun _ => 1

end WaveTurbulence

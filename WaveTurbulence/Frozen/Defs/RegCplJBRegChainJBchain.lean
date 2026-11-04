/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegCpl.JB, RegChain.JBchain (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.JB`: T Prop `regref2`
- `RegChain.JBchain`: (file) WAVE-B v2 §2.7; L826–L829; L848–L850

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **`𝒥ℬ*_𝒬(t, s)`** for a dominant couple code with all nodes in layer `r` (T Prop `regref2`,
(regref2-0), (regref2-1); route R4): trivial `1`; type 1 `2∫_r^{min(t,s)} ∏_j 𝒥ℬ*_{𝒬_j}(τ,τ) dτ`;
type 2 the iterated integral over `t > t₁ > ⋯ > t_{m₊} > r`, `s > s₁ > ⋯ > s_{m₋} > r` of the chain
couples' factors times `𝒥ℬ*_{𝒬_lp}(t_{m₊}, s_{m₋})` (`= 𝒥ℬ*_{𝒬_lp}(min(t_{m₊}, s_{m₋}))`, as `𝒬_lp` is
trivial or of type 1). Used for `t, s ∈ [r, r+1]`; values on non-dominant codes are not source
objects and are never used (`(K*)_app = 0` there). -/
noncomputable def RegCpl.JB (r : ℝ) : RegCpl → ℝ → ℝ → ℝ
  | .triv, _, _ => 1
  | .type1 _ Q₁ Q₂ Q₃, t, s => 2 * ∫ τ in r..min t s, Q₁.JB r τ τ * Q₂.JB r τ τ * Q₃.JB r τ τ
  | .type2 Xp Xm Qlp, t, s => Xp.JBchain r r t fun tm => Xm.JBchain r r s fun sm => Qlp.JB r tm sm

/-- Along a chain: `∫_{t > t₁ > ⋯ > t_m > lo} ∏_j ∏_ι 𝒥ℬ*_{𝒬_{j,ι}}(t_j, t_j) · G(t_m) dt` (pair `j`
of the chain gets the time `t_j`; `G(t)` for the empty chain). -/
noncomputable def RegChain.JBchain (r : ℝ) : RegChain → ℝ → ℝ → (ℝ → ℝ) → ℝ
  | .nil, _, t, G => G t
  | .pair _ Qr Qg _ rest, lo, t, G =>
    ∫ τ in lo..t, Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r lo τ G
end

end WaveTurbulence

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.IsCanonGC
public import WaveTurbulence.Frozen.Defs.KG
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsTrunc
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN

/-!
# truncSum

Wave B tier B1 (WaveB1-System.lean), source: T (expgarden), L762; T (ansatz3); WAVE-B v2 §2.4.3; T Def `defgtr`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **`truncSum q N t ζ⃗ n⃗`** (T (expgarden), L762, at time `t`; T (ansatz3)–(ansatz5) at `t = p`;
WAVE-B v2 §2.4.3): the sum of `K_𝒢(t, n⃗)` over `𝒢 ∈ 𝒢^tr_q` (width `≥ 4`) or `𝒬 ∈ 𝒞^tr_q`
(width 2) of signature `ζ⃗` and order `N`, truncation `(N_q, N_{q-1})` (T Def `defgtr`). A finite sum
(`finite_layeredGardens`). Then `𝒦^tr_{p+1,N}(t) = truncSum (p+1) N t`, and for `N ≤ N_p` the sums of
(ansatz3)–(ansatz5) are `truncSum p N p` (the truncation is void: audit lemma `truncSum_untruncated`). -/
noncomputable def truncSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) {w : ℕ} (t : ℝ)
    (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonGC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.sig = ζ ∧ LG.garden.order = N),
    KG P.L P.γ P.δ F LG t n

end WaveTurbulence

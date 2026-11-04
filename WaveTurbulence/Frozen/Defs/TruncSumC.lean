/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.IsCanonC
public import WaveTurbulence.Frozen.Defs.KQ
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsTrunc
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN

/-!
# truncSumC

Wave B tier B1 (WaveB1-System.lean), source: T L678. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **`truncSumC q N t k`**: the couple sum with real root vector `k` (T L678 with (expgarden), used
in (estcouple)): `∑ K_𝒬(t, k)` over `𝒬 ∈ 𝒞^tr_q` of order `N`. -/
noncomputable def truncSumC (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) (t : ℝ)
    (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : IsCanonC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.order = N),
    KQ P.L P.γ P.δ F LG t k

end WaveTurbulence

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplLinks
public import WaveTurbulence.Frozen.Defs.RegCplMstarRegChainNstar
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplTreesRegChainPlug
public import WaveTurbulence.Frozen.Defs.SpecialSets
public import WaveTurbulence.Frozen.Defs.SpecialWeight
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.ZetaOfTrees

/-!
# RegCpl.app

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref1-3); WAVE-B §2.7. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **The leading term `(K*_𝒬)_app(t, s, k)`** of a couple code with all nodes in layer `r` and input
`F = F_r` (T (regref1-3); WAVE-B §2.7 item 9, route R4, deviation D1 of B2.1):
`2^{-2n} δ^n ζ(𝒬) ∑_{Z special} ∏_{𝔫 ∈ Z} (−ζ_𝔫 π i)^{-1} 𝒥ℬ*_𝒬(t,s) ℳ*_{(𝒬,Z)}(k)[F]` for dominant
codes (`2n = n(𝒬)`), and `0` for non-dominant codes (T: non-dominant couples have no leading term).
Deviation (F61, B2-CL-11): the weight is `(−ζ_𝔫 π i)^{-1}` (`specialWeight`), not T's `(ζ_𝔫 π i)^{-1}`. -/
noncomputable def RegCpl.app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (t s : ℝ)
    (k : Mom d) : ℂ :=
  if Q.dominant then
    ((2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) *
      zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]) *
      ∑ Z ∈ specialSets Q.links, specialWeight ![1, -1] Z * (Q.JB r t s : ℂ) *
        (Q.Mstar F Z (0, []) (1, []) k : ℂ)
  else 0

end WaveTurbulence

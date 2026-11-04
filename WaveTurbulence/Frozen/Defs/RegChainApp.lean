/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RegChainJBtree
public import WaveTurbulence.Frozen.Defs.RegChainTreeLinks
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
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
# RegChain.app

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref1-3). Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **The leading term `(K*_𝒯)_app(t, s, k)`** of a tree code of sign `ζ` with all nodes except the
lone leaf in layer `r` (T (regref1-3), second line; (regref3-1-1)): `ℳ*_𝒯 = ∏_j 𝒩*_{(j,0)}`. Deviation (F61,
B2-CL-11): as for couples, the special-subset weight is `∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}` (`specialWeight`). -/
noncomputable def RegChain.app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) : ℂ :=
  if X.dominant then
    ((2 : ℂ)⁻¹ ^ X.size * (δ : ℂ) ^ (X.size / 2) * zetaOfTrees ![ζ] ![X.plug ζ .leaf]) *
      ∑ Z ∈ specialSets (X.treeLinks ζ), specialWeight ![ζ] Z * (X.JBtree r t s : ℂ) *
        (X.Nstar F Z ζ (0, []) k : ℂ)
  else 0

end WaveTurbulence

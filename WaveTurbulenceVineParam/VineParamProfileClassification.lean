/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamProfileDegrees
import WaveTurbulenceVineParam.VineParamProfileWrapper.I
import WaveTurbulenceVineParam.VineParamProfileWrapper.II
import WaveTurbulenceVineParam.VineParamProfileWrapper.III
import WaveTurbulenceVineParam.VineParamProfileWrapper.IV
import WaveTurbulenceVineParam.VineParamProfileWrapper.V
import WaveTurbulenceVineParam.VineParamProfileWrapper.VI
import WaveTurbulenceVineParam.VineParamProfileWrapper.VII
import WaveTurbulenceVineParam.VineParamProfileWrapper.VIII
import Mathlib.Tactic

/-! # Exhaustive source-balanced orientation classification for all eight bases -/

public section
namespace WaveTurbulence.Vine.Param

/-- Actual bundle multiplicity bounds and actual outgoing degree equations
produce a profile index in the literal complete catalogue. This covers
all eight pinned bases, including the four-atom type-II Q-block (F72). -/
theorem exists_base_profile (X : VineType) (k : Fin (baseBundles X).length → ℕ)
    (hk : ∀ i,k i ≤ ((baseBundles X)[i.1]'i.2).2)
    (hb : ∀ v : Fin X.template.n,baseOutgoing X k v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount X),baseProfileCounts X p=List.ofFn k := by
  cases X with
  | I => exact Profiles.I.exists_profile k hk hb
  | II => exact Profiles.II.exists_profile k hk hb
  | III => exact Profiles.III.exists_profile k hk hb
  | IV => exact Profiles.IV.exists_profile k hk hb
  | V => exact Profiles.V.exists_profile k hk hb
  | VI => exact Profiles.VI.exists_profile k hk hb
  | VII => exact Profiles.VII.exists_profile k hk hb
  | VIII => exact Profiles.VIII.exists_profile k hk hb

end WaveTurbulence.Vine.Param

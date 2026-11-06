/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Source degree constraints for normalized orientation counts -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Number of outgoing bonds at a literal atom for bundle direction counts.
Each bundle is stored in increasing endpoint order. -/
@[expose] def baseOutgoing (X : VineType) (k : Fin (baseBundles X).length → ℕ) (v : ℕ) : ℕ :=
  ∑ i : Fin (baseBundles X).length,
    if ((baseBundles X)[i.1]'i.2).1.1=v then k i
    else if ((baseBundles X)[i.1]'i.2).1.2=v then ((baseBundles X)[i.1]'i.2).2-k i else 0

/-- Parallel occurrences normalized by the actual profile direction counts. -/
@[expose] def normalizedBaseEnds (X : VineType) (p : Fin (baseProfileCount X)) : List (ℕ×ℕ) :=
  ((baseBundles X).zip (baseProfileCounts X p)).flatMap fun bk =>
    List.replicate bk.2 bk.1.1 ++ List.replicate (bk.1.2-bk.2) (bk.1.1.2,bk.1.1.1)

/-- The bundle count vector always has its complete source length. -/
theorem baseProfileCounts_length (X : VineType) : ∀ p,
    (baseProfileCounts X p).length=(baseBundles X).length := by
  cases X <;> decide

/-- Bundle endpoints are distinct old atoms. -/
theorem baseBundles_endpoints (X : VineType) : ∀ b ∈ baseBundles X,
    b.1.1<b.1.2 ∧ b.1.2<X.template.n ∧ 1 ≤ b.2 ∧ b.2 ≤ 2 := by
  cases X <;> decide

end WaveTurbulence.Vine.Param

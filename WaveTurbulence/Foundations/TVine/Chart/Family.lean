/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Contract
public import WaveTurbulenceVineParam.VineParamMain

/-!
# The chart contract for the `γ`-dependent vine family `𝒱_γ`

The de-indexed contract (`Chart.Contract`) for every member of `𝒱_γ` (pinned `Molecule.IsVineGamma`):
* the drawn vines (I)–(VIII) (`γ > 1/2`) and the bad vines (I), (II) (`γ ≤ 1/2`) get main's sealed charts
  (`Vine.Param.vineparam`, M9), de-indexed by `ofVineChart`;
* the T-vines (`γ ≤ 1/2`) get Theorem C (`TVineChartExists`).

So `VineGammaChartStatement` reduces to Theorem C. (By M4 §9 "Remark", the bad charts also follow from the rung
charts alone; main's catalogue is used here because it is sealed.)
-/

@[expose] public section

namespace WaveTurbulence.TVine.Chart

open VineParamContract

/-- **The `𝒱_γ` chart contract from Theorem C.** -/
theorem vineGammaChart_of_tvine (hT : TVineChartExists) : VineGammaChartStatement := by
  intro γ V D _ _ _ M hM S a b hV
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · obtain ⟨F⟩ := Vine.Param.vineparam V D M hM .I S a b h
      exact ⟨ofVineChart F⟩
    · obtain ⟨F⟩ := Vine.Param.vineparam V D M hM .II S a b h
      exact ⟨ofVineChart F⟩
  · intro hnb
    rcases hV with ⟨-, hE⟩ | ⟨-, X, hX⟩
    · rcases hE with h | h | h
      · exact absurd (Or.inl h) hnb
      · exact absurd (Or.inr h) hnb
      · exact hT V D M hM S a b h
    · obtain ⟨F⟩ := Vine.Param.vineparam V D M hM X S a b hX
      cases X with
      | I => exact absurd (Or.inl hX) hnb
      | II => exact absurd (Or.inr hX) hnb
      | III => exact ⟨ofVineChart F⟩
      | IV => exact ⟨ofVineChart F⟩
      | V => exact ⟨ofVineChart F⟩
      | VI => exact ⟨ofVineChart F⟩
      | VII => exact ⟨ofVineChart F⟩
      | VIII => exact ⟨ofVineChart F⟩

end WaveTurbulence.TVine.Chart

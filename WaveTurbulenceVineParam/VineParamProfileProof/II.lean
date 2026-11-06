/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine II

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.II

private theorem case0 (q0 q1 q2 q3 q4 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 2) (h3 : q3 ≤ 1) (h4 : q4 ≤ 1) (hb0 : q0+q1=1) (hb1 : q3+q4=1) (hb2 : (1-q0)+q2+(1-q3)=2) (hb3 : (1-q1)+(2-q2)+(1-q4)=2) :
    ∃ p : Fin (baseProfileCount .II),baseProfileCounts .II p=[q0,q1,q2,q3,q4] := by
  interval_cases q0
  · have he : q1=1 := by omega
    subst q1
    interval_cases q2
    · have he : q3=0 := by omega
      subst q3
      have he : q4=1 := by omega
      subst q4
      exact ⟨⟨0,by decide⟩,rfl⟩
    · have he : q3=1 := by omega
      subst q3
      have he : q4=0 := by omega
      subst q4
      exact ⟨⟨1,by decide⟩,rfl⟩
    · omega
  · have he : q1=0 := by omega
    subst q1
    interval_cases q2
    · omega
    · have he : q3=0 := by omega
      subst q3
      have he : q4=1 := by omega
      subst q4
      exact ⟨⟨2,by decide⟩,rfl⟩
    · have he : q3=1 := by omega
      subst q3
      have he : q4=0 := by omega
      subst q4
      exact ⟨⟨3,by decide⟩,rfl⟩

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 q1 q2 q3 q4 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 2) (h3 : q3 ≤ 1) (h4 : q4 ≤ 1) (hb0 : q0+q1=1) (hb1 : q3+q4=1) (hb2 : (1-q0)+q2+(1-q3)=2) (hb3 : (1-q1)+(2-q2)+(1-q4)=2) :
    ∃ p : Fin (baseProfileCount .II),baseProfileCounts .II p=[q0,q1,q2,q3,q4] := by
  exact case0 q0 q1 q2 q3 q4 h0 h1 h2 h3 h4 hb0 hb1 hb2 hb3

end WaveTurbulence.Vine.Param.Profiles.II

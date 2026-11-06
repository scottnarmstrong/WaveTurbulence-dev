/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine V

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.V

private theorem case0 (q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (h4 : q4 ≤ 2) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 2) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (hb2 : (1-1)+1+q10=2) (hb3 : (1-0)+(2-1)+q11=2) (hb4 : q4+q5+(1-q10)=2) (hb5 : (2-q4)+q6+(1-q11)=2) (hb6 : (1-q5)+q7+q8=2) (hb7 : (1-q6)+(1-q7)+q9=2) (hb8 : (2-q8)+(2-q9)=2) :
    ∃ p : Fin (baseProfileCount .V),baseProfileCounts .V p=[0,1,0,1,q4,q5,q6,q7,q8,q9,q10,q11] := by
  interval_cases q4
  · omega
  · have he : q5=1 := by omega
    subst q5
    have he : q6=0 := by omega
    subst q6
    interval_cases q7
    · have he : q8=2 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨0,by decide⟩,rfl⟩
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨1,by decide⟩,rfl⟩
  · have he : q5=0 := by omega
    subst q5
    have he : q6=1 := by omega
    subst q6
    interval_cases q7
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨2,by decide⟩,rfl⟩
    · have he : q8=0 := by omega
      subst q8
      have he : q9=2 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨3,by decide⟩,rfl⟩

private theorem case1 (q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (h4 : q4 ≤ 2) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 2) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (hb2 : (1-1)+2+q10=2) (hb3 : (1-0)+(2-2)+q11=2) (hb4 : q4+q5+(1-q10)=2) (hb5 : (2-q4)+q6+(1-q11)=2) (hb6 : (1-q5)+q7+q8=2) (hb7 : (1-q6)+(1-q7)+q9=2) (hb8 : (2-q8)+(2-q9)=2) :
    ∃ p : Fin (baseProfileCount .V),baseProfileCounts .V p=[0,1,0,2,q4,q5,q6,q7,q8,q9,q10,q11] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    have he : q6=0 := by omega
    subst q6
    interval_cases q7
    · have he : q8=2 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨4,by decide⟩,rfl⟩
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨5,by decide⟩,rfl⟩
  · have he : q5=0 := by omega
    subst q5
    have he : q6=1 := by omega
    subst q6
    interval_cases q7
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨6,by decide⟩,rfl⟩
    · have he : q8=0 := by omega
      subst q8
      have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨7,by decide⟩,rfl⟩
  · omega

private theorem case2 (q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (h4 : q4 ≤ 2) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 2) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (hb2 : (1-0)+0+q10=2) (hb3 : (1-1)+(2-0)+q11=2) (hb4 : q4+q5+(1-q10)=2) (hb5 : (2-q4)+q6+(1-q11)=2) (hb6 : (1-q5)+q7+q8=2) (hb7 : (1-q6)+(1-q7)+q9=2) (hb8 : (2-q8)+(2-q9)=2) :
    ∃ p : Fin (baseProfileCount .V),baseProfileCounts .V p=[1,0,1,0,q4,q5,q6,q7,q8,q9,q10,q11] := by
  interval_cases q4
  · omega
  · have he : q5=1 := by omega
    subst q5
    have he : q6=0 := by omega
    subst q6
    interval_cases q7
    · have he : q8=2 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨8,by decide⟩,rfl⟩
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨9,by decide⟩,rfl⟩
  · have he : q5=0 := by omega
    subst q5
    have he : q6=1 := by omega
    subst q6
    interval_cases q7
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨10,by decide⟩,rfl⟩
    · have he : q8=0 := by omega
      subst q8
      have he : q9=2 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      exact ⟨⟨11,by decide⟩,rfl⟩

private theorem case3 (q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (h4 : q4 ≤ 2) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 2) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (hb2 : (1-0)+1+q10=2) (hb3 : (1-1)+(2-1)+q11=2) (hb4 : q4+q5+(1-q10)=2) (hb5 : (2-q4)+q6+(1-q11)=2) (hb6 : (1-q5)+q7+q8=2) (hb7 : (1-q6)+(1-q7)+q9=2) (hb8 : (2-q8)+(2-q9)=2) :
    ∃ p : Fin (baseProfileCount .V),baseProfileCounts .V p=[1,0,1,1,q4,q5,q6,q7,q8,q9,q10,q11] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    have he : q6=0 := by omega
    subst q6
    interval_cases q7
    · have he : q8=2 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨12,by decide⟩,rfl⟩
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨13,by decide⟩,rfl⟩
  · have he : q5=0 := by omega
    subst q5
    have he : q6=1 := by omega
    subst q6
    interval_cases q7
    · have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨14,by decide⟩,rfl⟩
    · have he : q8=0 := by omega
      subst q8
      have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      exact ⟨⟨15,by decide⟩,rfl⟩
  · omega

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 1) (h3 : q3 ≤ 2) (h4 : q4 ≤ 2) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 2) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (hb0 : q0+q1=1) (hb1 : (1-q0)+q2=1) (hb2 : (1-q1)+q3+q10=2) (hb3 : (1-q2)+(2-q3)+q11=2) (hb4 : q4+q5+(1-q10)=2) (hb5 : (2-q4)+q6+(1-q11)=2) (hb6 : (1-q5)+q7+q8=2) (hb7 : (1-q6)+(1-q7)+q9=2) (hb8 : (2-q8)+(2-q9)=2) :
    ∃ p : Fin (baseProfileCount .V),baseProfileCounts .V p=[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11] := by
  interval_cases q0
  · have he : q1=1 := by omega
    subst q1
    have he : q2=0 := by omega
    subst q2
    interval_cases q3
    · omega
    · exact case0 q4 q5 q6 q7 q8 q9 q10 q11 h4 h5 h6 h7 h8 h9 h10 h11 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · exact case1 q4 q5 q6 q7 q8 q9 q10 q11 h4 h5 h6 h7 h8 h9 h10 h11 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  · have he : q1=0 := by omega
    subst q1
    have he : q2=1 := by omega
    subst q2
    interval_cases q3
    · exact case2 q4 q5 q6 q7 q8 q9 q10 q11 h4 h5 h6 h7 h8 h9 h10 h11 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · exact case3 q4 q5 q6 q7 q8 q9 q10 q11 h4 h5 h6 h7 h8 h9 h10 h11 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · omega

end WaveTurbulence.Vine.Param.Profiles.V

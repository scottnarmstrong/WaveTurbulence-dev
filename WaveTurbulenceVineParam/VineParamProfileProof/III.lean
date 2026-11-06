/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine III

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.III

private theorem case0 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-0)+0+q9=2) (hb3 : (1-1)+(2-0)+q10=2) (hb4 : 0+q4+(1-q9)+q11=2) (hb5 : (1-0)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[0,1,0,0,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  interval_cases q6
  · omega
  · have he : q7=0 := by omega
    subst q7
    have he : q8=1 := by omega
    subst q8
    have he : q9=1 := by omega
    subst q9
    have he : q10=0 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    have he : q12=0 := by omega
    subst q12
    exact ⟨⟨0,by decide⟩,rfl⟩
  · have he : q7=1 := by omega
    subst q7
    have he : q8=0 := by omega
    subst q8
    have he : q9=1 := by omega
    subst q9
    have he : q10=0 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    have he : q12=0 := by omega
    subst q12
    exact ⟨⟨1,by decide⟩,rfl⟩

private theorem case1 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-0)+0+q9=2) (hb3 : (1-1)+(2-0)+q10=2) (hb4 : 1+q4+(1-q9)+q11=2) (hb5 : (1-1)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[0,1,0,1,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · omega
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨2,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨3,by decide⟩,rfl⟩
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨4,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨5,by decide⟩,rfl⟩
    · omega

private theorem case2 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-0)+1+q9=2) (hb3 : (1-1)+(2-1)+q10=2) (hb4 : 0+q4+(1-q9)+q11=2) (hb5 : (1-0)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[0,1,1,0,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · omega
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨6,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨7,by decide⟩,rfl⟩
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨8,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨9,by decide⟩,rfl⟩
    · omega

private theorem case3 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-0)+1+q9=2) (hb3 : (1-1)+(2-1)+q10=2) (hb4 : 1+q4+(1-q9)+q11=2) (hb5 : (1-1)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[0,1,1,1,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=2 := by omega
  subst q5
  interval_cases q6
  · have he : q7=0 := by omega
    subst q7
    have he : q8=1 := by omega
    subst q8
    have he : q9=0 := by omega
    subst q9
    have he : q10=1 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    have he : q12=1 := by omega
    subst q12
    exact ⟨⟨10,by decide⟩,rfl⟩
  · have he : q7=1 := by omega
    subst q7
    have he : q8=0 := by omega
    subst q8
    have he : q9=0 := by omega
    subst q9
    have he : q10=1 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    have he : q12=1 := by omega
    subst q12
    exact ⟨⟨11,by decide⟩,rfl⟩
  · omega

private theorem case4 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-1)+1+q9=2) (hb3 : (1-0)+(2-1)+q10=2) (hb4 : 0+q4+(1-q9)+q11=2) (hb5 : (1-0)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[1,0,1,0,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  interval_cases q6
  · omega
  · have he : q7=0 := by omega
    subst q7
    have he : q8=1 := by omega
    subst q8
    have he : q9=1 := by omega
    subst q9
    have he : q10=0 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    have he : q12=0 := by omega
    subst q12
    exact ⟨⟨12,by decide⟩,rfl⟩
  · have he : q7=1 := by omega
    subst q7
    have he : q8=0 := by omega
    subst q8
    have he : q9=1 := by omega
    subst q9
    have he : q10=0 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    have he : q12=0 := by omega
    subst q12
    exact ⟨⟨13,by decide⟩,rfl⟩

private theorem case5 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-1)+1+q9=2) (hb3 : (1-0)+(2-1)+q10=2) (hb4 : 1+q4+(1-q9)+q11=2) (hb5 : (1-1)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[1,0,1,1,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · omega
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨14,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨15,by decide⟩,rfl⟩
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨16,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=1 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨17,by decide⟩,rfl⟩
    · omega

private theorem case6 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-1)+2+q9=2) (hb3 : (1-0)+(2-2)+q10=2) (hb4 : 0+q4+(1-q9)+q11=2) (hb5 : (1-0)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[1,0,2,0,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  interval_cases q4
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · omega
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨18,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      exact ⟨⟨19,by decide⟩,rfl⟩
  · have he : q5=1 := by omega
    subst q5
    interval_cases q6
    · have he : q7=0 := by omega
      subst q7
      have he : q8=1 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨20,by decide⟩,rfl⟩
    · have he : q7=1 := by omega
      subst q7
      have he : q8=0 := by omega
      subst q8
      have he : q9=0 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      exact ⟨⟨21,by decide⟩,rfl⟩
    · omega

private theorem case7 (q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb1 : q7+q8=1) (hb2 : (1-1)+2+q9=2) (hb3 : (1-0)+(2-2)+q10=2) (hb4 : 1+q4+(1-q9)+q11=2) (hb5 : (1-1)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[1,0,2,1,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=2 := by omega
  subst q5
  interval_cases q6
  · have he : q7=0 := by omega
    subst q7
    have he : q8=1 := by omega
    subst q8
    have he : q9=0 := by omega
    subst q9
    have he : q10=1 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    have he : q12=1 := by omega
    subst q12
    exact ⟨⟨22,by decide⟩,rfl⟩
  · have he : q7=1 := by omega
    subst q7
    have he : q8=0 := by omega
    subst q8
    have he : q9=0 := by omega
    subst q9
    have he : q10=1 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    have he : q12=1 := by omega
    subst q12
    exact ⟨⟨23,by decide⟩,rfl⟩
  · omega

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 2) (h3 : q3 ≤ 1) (h4 : q4 ≤ 1) (h5 : q5 ≤ 2) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 1) (h9 : q9 ≤ 1) (h10 : q10 ≤ 1) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (hb0 : q0+q1=1) (hb1 : q7+q8=1) (hb2 : (1-q0)+q2+q9=2) (hb3 : (1-q1)+(2-q2)+q10=2) (hb4 : q3+q4+(1-q9)+q11=2) (hb5 : (1-q3)+q5+(1-q10)=2) (hb6 : (1-q4)+(2-q5)+q12=2) (hb7 : q6+(1-q7)+(1-q11)=2) (hb8 : (2-q6)+(1-q8)+(1-q12)=2) :
    ∃ p : Fin (baseProfileCount .III),baseProfileCounts .III p=[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12] := by
  interval_cases q0
  · have he : q1=1 := by omega
    subst q1
    interval_cases q2
    · interval_cases q3
      · exact case0 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
      · exact case1 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · interval_cases q3
      · exact case2 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
      · exact case3 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · omega
  · have he : q1=0 := by omega
    subst q1
    interval_cases q2
    · omega
    · interval_cases q3
      · exact case4 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
      · exact case5 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
    · interval_cases q3
      · exact case6 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
      · exact case7 q4 q5 q6 q7 q8 q9 q10 q11 q12 h4 h5 h6 h7 h8 h9 h10 h11 h12 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8

end WaveTurbulence.Vine.Param.Profiles.III

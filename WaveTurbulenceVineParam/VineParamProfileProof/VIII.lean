/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine VIII

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.VIII

private theorem case0 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-0)+0+q11=2) (hb3 : (2-0)+q6+q12=2) (hb4 : 1+(1-q4)+(1-q11)=2) (hb5 : (2-1)+(1-q5)+(1-q12)=2) (hb6 : (1-1)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[0,1,0,1,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=1 := by omega
  subst q5
  have he : q6=0 := by omega
  subst q6
  interval_cases q7
  · omega
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨0,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨1,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨2,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨3,by decide⟩,rfl⟩

private theorem case1 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-0)+0+q11=2) (hb3 : (2-0)+q6+q12=2) (hb4 : 2+(1-q4)+(1-q11)=2) (hb5 : (2-2)+(1-q5)+(1-q12)=2) (hb6 : (1-1)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[0,1,0,2,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  have he : q6=0 := by omega
  subst q6
  interval_cases q7
  · omega
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨4,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨5,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨6,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨7,by decide⟩,rfl⟩

private theorem case2 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-0)+1+q11=2) (hb3 : (2-1)+q6+q12=2) (hb4 : 0+(1-q4)+(1-q11)=2) (hb5 : (2-0)+(1-q5)+(1-q12)=2) (hb6 : (1-1)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[0,1,1,0,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=1 := by omega
  subst q5
  have he : q6=0 := by omega
  subst q6
  interval_cases q7
  · omega
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨8,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨9,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨10,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨11,by decide⟩,rfl⟩

private theorem case3 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-0)+1+q11=2) (hb3 : (2-1)+q6+q12=2) (hb4 : 1+(1-q4)+(1-q11)=2) (hb5 : (2-1)+(1-q5)+(1-q12)=2) (hb6 : (1-1)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[0,1,1,1,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  have he : q6=0 := by omega
  subst q6
  interval_cases q7
  · omega
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨12,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨13,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨14,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨15,by decide⟩,rfl⟩

private theorem case4 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-1)+1+q11=2) (hb3 : (2-1)+q6+q12=2) (hb4 : 1+(1-q4)+(1-q11)=2) (hb5 : (2-1)+(1-q5)+(1-q12)=2) (hb6 : (1-0)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[1,0,1,1,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=1 := by omega
  subst q5
  have he : q6=1 := by omega
  subst q6
  interval_cases q7
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨16,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨17,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨18,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨19,by decide⟩,rfl⟩
  · omega

private theorem case5 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-1)+1+q11=2) (hb3 : (2-1)+q6+q12=2) (hb4 : 2+(1-q4)+(1-q11)=2) (hb5 : (2-2)+(1-q5)+(1-q12)=2) (hb6 : (1-0)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[1,0,1,2,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  have he : q6=1 := by omega
  subst q6
  interval_cases q7
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨20,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨21,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨22,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=1 := by omega
      subst q11
      have he : q12=0 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨23,by decide⟩,rfl⟩
  · omega

private theorem case6 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-1)+2+q11=2) (hb3 : (2-2)+q6+q12=2) (hb4 : 0+(1-q4)+(1-q11)=2) (hb5 : (2-0)+(1-q5)+(1-q12)=2) (hb6 : (1-0)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[1,0,2,0,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=0 := by omega
  subst q4
  have he : q5=1 := by omega
  subst q5
  have he : q6=1 := by omega
  subst q6
  interval_cases q7
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨24,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨25,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨26,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨27,by decide⟩,rfl⟩
  · omega

private theorem case7 (q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb1 : q4+q5=1) (hb2 : (1-1)+2+q11=2) (hb3 : (2-2)+q6+q12=2) (hb4 : 1+(1-q4)+(1-q11)=2) (hb5 : (2-1)+(1-q5)+(1-q12)=2) (hb6 : (1-0)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[1,0,2,1,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  have he : q4=1 := by omega
  subst q4
  have he : q5=0 := by omega
  subst q5
  have he : q6=1 := by omega
  subst q6
  interval_cases q7
  · interval_cases q8
    · have he : q9=2 := by omega
      subst q9
      have he : q10=0 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨28,by decide⟩,rfl⟩
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      exact ⟨⟨29,by decide⟩,rfl⟩
  · interval_cases q8
    · have he : q9=1 := by omega
      subst q9
      have he : q10=1 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨30,by decide⟩,rfl⟩
    · have he : q9=0 := by omega
      subst q9
      have he : q10=2 := by omega
      subst q10
      have he : q11=0 := by omega
      subst q11
      have he : q12=1 := by omega
      subst q12
      have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      exact ⟨⟨31,by decide⟩,rfl⟩
  · omega

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 2) (h3 : q3 ≤ 2) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 1) (h7 : q7 ≤ 2) (h8 : q8 ≤ 1) (h9 : q9 ≤ 2) (h10 : q10 ≤ 2) (h11 : q11 ≤ 1) (h12 : q12 ≤ 1) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (hb0 : q0+q1=1) (hb1 : q4+q5=1) (hb2 : (1-q0)+q2+q11=2) (hb3 : (2-q2)+q6+q12=2) (hb4 : q3+(1-q4)+(1-q11)=2) (hb5 : (2-q3)+(1-q5)+(1-q12)=2) (hb6 : (1-q1)+q7+q13=2) (hb7 : (1-q6)+(2-q7)+q14=2) (hb8 : q8+q9+(1-q13)=2) (hb9 : (1-q8)+q10+(1-q14)=2) (hb10 : (2-q9)+(2-q10)=2) :
    ∃ p : Fin (baseProfileCount .VIII),baseProfileCounts .VIII p=[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14] := by
  interval_cases q0
  · have he : q1=1 := by omega
    subst q1
    interval_cases q2
    · interval_cases q3
      · omega
      · exact case0 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · exact case1 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
    · interval_cases q3
      · exact case2 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · exact case3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · omega
    · omega
  · have he : q1=0 := by omega
    subst q1
    interval_cases q2
    · omega
    · interval_cases q3
      · omega
      · exact case4 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · exact case5 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
    · interval_cases q3
      · exact case6 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · exact case7 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
      · omega

end WaveTurbulence.Vine.Param.Profiles.VIII

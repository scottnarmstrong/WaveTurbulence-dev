/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine VI

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.VI

theorem case28 (q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : ℕ) (h9 : q9 ≤ 1) (h10 : q10 ≤ 2) (h11 : q11 ≤ 2) (h12 : q12 ≤ 2) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (h15 : q15 ≤ 1) (h16 : q16 ≤ 1) (h17 : q17 ≤ 1) (h18 : q18 ≤ 1) (h19 : q19 ≤ 1) (h20 : q20 ≤ 1) (hb1 : q13+q14=1) (hb2 : (1-1)+2+q15=2) (hb3 : (1-0)+(2-2)+q16=2) (hb4 : 1+0+(1-q15)=2) (hb5 : (2-1)+1+(1-q16)=2) (hb6 : (1-0)+0+q19=2) (hb7 : (2-0)+0+q20=2) (hb8 : (1-1)+1+q17=2) (hb9 : (1-0)+(2-1)+q18=2) (hb10 : q9+q10+(1-q17)=2) (hb11 : (1-q9)+q11+(1-q18)=2) (hb12 : (2-q10)+(2-q11)=2) (hb13 : q12+(1-q13)+(1-q19)=2) (hb14 : (2-q12)+(1-q14)+(1-q20)=2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=[1,0,2,1,0,1,0,0,1,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20] := by
  interval_cases q9
  · have he : q10=2 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    interval_cases q12
    · omega
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨112,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨113,by decide⟩,rfl⟩
  · have he : q10=1 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    interval_cases q12
    · omega
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨114,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨115,by decide⟩,rfl⟩

theorem case29 (q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : ℕ) (h9 : q9 ≤ 1) (h10 : q10 ≤ 2) (h11 : q11 ≤ 2) (h12 : q12 ≤ 2) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (h15 : q15 ≤ 1) (h16 : q16 ≤ 1) (h17 : q17 ≤ 1) (h18 : q18 ≤ 1) (h19 : q19 ≤ 1) (h20 : q20 ≤ 1) (hb1 : q13+q14=1) (hb2 : (1-1)+2+q15=2) (hb3 : (1-0)+(2-2)+q16=2) (hb4 : 1+0+(1-q15)=2) (hb5 : (2-1)+1+(1-q16)=2) (hb6 : (1-0)+0+q19=2) (hb7 : (2-0)+0+q20=2) (hb8 : (1-1)+2+q17=2) (hb9 : (1-0)+(2-2)+q18=2) (hb10 : q9+q10+(1-q17)=2) (hb11 : (1-q9)+q11+(1-q18)=2) (hb12 : (2-q10)+(2-q11)=2) (hb13 : q12+(1-q13)+(1-q19)=2) (hb14 : (2-q12)+(1-q14)+(1-q20)=2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=[1,0,2,1,0,1,0,0,2,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20] := by
  interval_cases q9
  · have he : q10=1 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    interval_cases q12
    · omega
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨116,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨117,by decide⟩,rfl⟩
  · have he : q10=0 := by omega
    subst q10
    have he : q11=2 := by omega
    subst q11
    interval_cases q12
    · omega
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨118,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=1 := by omega
      subst q19
      have he : q20=0 := by omega
      subst q20
      exact ⟨⟨119,by decide⟩,rfl⟩

theorem case30 (q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : ℕ) (h9 : q9 ≤ 1) (h10 : q10 ≤ 2) (h11 : q11 ≤ 2) (h12 : q12 ≤ 2) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (h15 : q15 ≤ 1) (h16 : q16 ≤ 1) (h17 : q17 ≤ 1) (h18 : q18 ≤ 1) (h19 : q19 ≤ 1) (h20 : q20 ≤ 1) (hb1 : q13+q14=1) (hb2 : (1-1)+2+q15=2) (hb3 : (1-0)+(2-2)+q16=2) (hb4 : 1+0+(1-q15)=2) (hb5 : (2-1)+1+(1-q16)=2) (hb6 : (1-0)+1+q19=2) (hb7 : (2-1)+0+q20=2) (hb8 : (1-1)+1+q17=2) (hb9 : (1-0)+(2-1)+q18=2) (hb10 : q9+q10+(1-q17)=2) (hb11 : (1-q9)+q11+(1-q18)=2) (hb12 : (2-q10)+(2-q11)=2) (hb13 : q12+(1-q13)+(1-q19)=2) (hb14 : (2-q12)+(1-q14)+(1-q20)=2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=[1,0,2,1,0,1,1,0,1,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20] := by
  interval_cases q9
  · have he : q10=2 := by omega
    subst q10
    have he : q11=0 := by omega
    subst q11
    interval_cases q12
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨120,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨121,by decide⟩,rfl⟩
    · omega
  · have he : q10=1 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    interval_cases q12
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨122,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=1 := by omega
      subst q17
      have he : q18=0 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨123,by decide⟩,rfl⟩
    · omega

theorem case31 (q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : ℕ) (h9 : q9 ≤ 1) (h10 : q10 ≤ 2) (h11 : q11 ≤ 2) (h12 : q12 ≤ 2) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (h15 : q15 ≤ 1) (h16 : q16 ≤ 1) (h17 : q17 ≤ 1) (h18 : q18 ≤ 1) (h19 : q19 ≤ 1) (h20 : q20 ≤ 1) (hb1 : q13+q14=1) (hb2 : (1-1)+2+q15=2) (hb3 : (1-0)+(2-2)+q16=2) (hb4 : 1+0+(1-q15)=2) (hb5 : (2-1)+1+(1-q16)=2) (hb6 : (1-0)+1+q19=2) (hb7 : (2-1)+0+q20=2) (hb8 : (1-1)+2+q17=2) (hb9 : (1-0)+(2-2)+q18=2) (hb10 : q9+q10+(1-q17)=2) (hb11 : (1-q9)+q11+(1-q18)=2) (hb12 : (2-q10)+(2-q11)=2) (hb13 : q12+(1-q13)+(1-q19)=2) (hb14 : (2-q12)+(1-q14)+(1-q20)=2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=[1,0,2,1,0,1,1,0,2,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20] := by
  interval_cases q9
  · have he : q10=1 := by omega
    subst q10
    have he : q11=1 := by omega
    subst q11
    interval_cases q12
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨124,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨125,by decide⟩,rfl⟩
    · omega
  · have he : q10=0 := by omega
    subst q10
    have he : q11=2 := by omega
    subst q11
    interval_cases q12
    · have he : q13=0 := by omega
      subst q13
      have he : q14=1 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨126,by decide⟩,rfl⟩
    · have he : q13=1 := by omega
      subst q13
      have he : q14=0 := by omega
      subst q14
      have he : q15=0 := by omega
      subst q15
      have he : q16=1 := by omega
      subst q16
      have he : q17=0 := by omega
      subst q17
      have he : q18=1 := by omega
      subst q18
      have he : q19=0 := by omega
      subst q19
      have he : q20=1 := by omega
      subst q20
      exact ⟨⟨127,by decide⟩,rfl⟩
    · omega

end WaveTurbulence.Vine.Param.Profiles.VI

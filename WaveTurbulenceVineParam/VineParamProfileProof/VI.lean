/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part0
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part1
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part2
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part3
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part4
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part5
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part6
import WaveTurbulenceVineParam.VineParamProfileProof.VI.Part7
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine VI

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.VI

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : ℕ) (h0 : q0 ≤ 1) (h1 : q1 ≤ 1) (h2 : q2 ≤ 2) (h3 : q3 ≤ 2) (h4 : q4 ≤ 1) (h5 : q5 ≤ 1) (h6 : q6 ≤ 2) (h7 : q7 ≤ 1) (h8 : q8 ≤ 2) (h9 : q9 ≤ 1) (h10 : q10 ≤ 2) (h11 : q11 ≤ 2) (h12 : q12 ≤ 2) (h13 : q13 ≤ 1) (h14 : q14 ≤ 1) (h15 : q15 ≤ 1) (h16 : q16 ≤ 1) (h17 : q17 ≤ 1) (h18 : q18 ≤ 1) (h19 : q19 ≤ 1) (h20 : q20 ≤ 1) (hb0 : q0+q1=1) (hb1 : q13+q14=1) (hb2 : (1-q0)+q2+q15=2) (hb3 : (1-q1)+(2-q2)+q16=2) (hb4 : q3+q4+(1-q15)=2) (hb5 : (2-q3)+q5+(1-q16)=2) (hb6 : (1-q4)+q6+q19=2) (hb7 : (2-q6)+q7+q20=2) (hb8 : (1-q5)+q8+q17=2) (hb9 : (1-q7)+(2-q8)+q18=2) (hb10 : q9+q10+(1-q17)=2) (hb11 : (1-q9)+q11+(1-q18)=2) (hb12 : (2-q10)+(2-q11)=2) (hb13 : q12+(1-q13)+(1-q19)=2) (hb14 : (2-q12)+(1-q14)+(1-q20)=2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20] := by
  interval_cases q0
  · have he : q1=1 := by omega
    subst q1
    interval_cases q2
    · interval_cases q3
      · omega
      · have he : q4=1 := by omega
        subst q4
        have he : q5=0 := by omega
        subst q5
        interval_cases q6
        · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case0 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case1 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case2 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case3 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
      · have he : q4=0 := by omega
        subst q4
        have he : q5=1 := by omega
        subst q5
        interval_cases q6
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case4 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case5 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case6 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · omega
    · interval_cases q3
      · have he : q4=1 := by omega
        subst q4
        have he : q5=0 := by omega
        subst q5
        interval_cases q6
        · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case9 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case10 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case11 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
      · have he : q4=0 := by omega
        subst q4
        have he : q5=1 := by omega
        subst q5
        interval_cases q6
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case12 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case13 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case14 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case15 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · omega
      · omega
    · omega
  · have he : q1=0 := by omega
    subst q1
    interval_cases q2
    · omega
    · interval_cases q3
      · omega
      · have he : q4=1 := by omega
        subst q4
        have he : q5=0 := by omega
        subst q5
        interval_cases q6
        · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case16 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case17 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case18 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case19 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
      · have he : q4=0 := by omega
        subst q4
        have he : q5=1 := by omega
        subst q5
        interval_cases q6
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case20 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case21 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case22 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case23 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · omega
    · interval_cases q3
      · have he : q4=1 := by omega
        subst q4
        have he : q5=0 := by omega
        subst q5
        interval_cases q6
        · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case24 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case25 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
        · have he : q7=1 := by omega
          subst q7
          interval_cases q8
          · exact case26 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case27 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · omega
      · have he : q4=0 := by omega
        subst q4
        have he : q5=1 := by omega
        subst q5
        interval_cases q6
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case28 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case29 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · have he : q7=0 := by omega
          subst q7
          interval_cases q8
          · omega
          · exact case30 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
          · exact case31 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
        · omega
      · omega

end WaveTurbulence.Vine.Param.Profiles.VI

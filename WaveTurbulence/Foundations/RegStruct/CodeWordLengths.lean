/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeWords

/-! # Linear prefix-word bounds for well-formed structure data (DH21 Corollary 4.9) -/

public section

namespace WaveTurbulence.Reg

mutual
/-- A well-formed couple has a prefix description of length at most four times its order plus one. -/
theorem coupleWord_length (Q : RegCpl) (hw : Q.wf = true) :
    (coupleWord Q).length ≤ 4 * Q.size + 1 := by
  cases Q with
  | triv => decide
  | type1 c a b d =>
    simp only [RegCpl.wf, Bool.and_eq_true] at hw
    have ha := coupleWord_length a hw.1.1
    have hb := coupleWord_length b hw.1.2
    have hd := coupleWord_length d hw.2
    simp only [coupleWord, List.length_cons, List.length_append, RegCpl.size]
    omega
  | type2 x y q =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hx,hx'⟩ := chainWord_length x hw.1.1.1.1
    obtain ⟨hy,hy'⟩ := chainWord_length y hw.1.1.1.2
    have hq := coupleWord_length q hw.1.1.2
    simp only [coupleWord, List.length_cons, List.length_append, RegCpl.size]
    rcases Bool.and_eq_false_iff.mp hw.2 with hx0 | hy0
    · have := hx' hx0
      omega
    · have := hy' hy0
      omega
termination_by structural Q

/-- Empty chains use one token; nonempty chains have enough positive order to absorb
constructor overhead in an enclosing type-2 couple. -/
theorem chainWord_length (X : RegChain) (hw : X.wf = true) :
    (chainWord X).length ≤ 4 * X.size + 1 ∧
      (X.isNil = false → (chainWord X).length + 3 ≤ 4 * X.size) := by
  cases X with
  | nil => simp [chainWord, RegChain.size, RegChain.isNil]
  | pair m r g i s =>
    simp only [RegChain.wf, Bool.and_eq_true] at hw
    have hr := coupleWord_length r hw.1.1.1
    have hg := coupleWord_length g hw.1.1.2
    have hi := (chainWord_length i hw.1.2).1
    have hs := (chainWord_length s hw.2).1
    simp only [chainWord, List.length_cons, List.length_append, RegChain.size, RegChain.isNil]
    constructor <;> omega
termination_by structural X
end

end WaveTurbulence.Reg

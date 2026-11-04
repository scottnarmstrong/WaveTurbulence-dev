/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.NormalizeCodes

/-! # Normalization fixes exactly the well-formed code interface (DH21 Proposition 4.10) -/

public section
namespace WaveTurbulence.Reg

/-- A terminal non-type-2 couple with nonempty outer chains is already normalized at the root. -/
theorem attachChains_eq_type2 (Xp Xm : RegChain) (Q : RegCpl)
    (ht : Q.isType2 = false) (hn : (Xp.isNil && Xm.isNil) = false) :
    attachChains Xp Xm Q = .type2 Xp Xm Q := by
  cases Q with
  | triv => simp only [attachChains, joinChains, hn, Bool.false_eq_true, ↓reduceIte]
  | type1 c a b d => simp only [attachChains, joinChains, hn, Bool.false_eq_true, ↓reduceIte]
  | type2 p m q => simp only [RegCpl.isType2, Bool.true_eq_false] at ht

mutual
/-- Every well-formed couple code is fixed by normalization. -/
theorem normalizeCouple_eq_self (Q : RegCpl) (hw : Q.wf = true) : normalizeCouple Q = Q := by
  cases Q with
  | triv => rfl
  | type1 c a b d =>
    simp only [RegCpl.wf, Bool.and_eq_true] at hw
    simp only [normalizeCouple, normalizeCouple_eq_self a hw.1.1,
      normalizeCouple_eq_self b hw.1.2, normalizeCouple_eq_self d hw.2]
  | type2 p m q =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [normalizeCouple, normalizeChain_eq_self p hw.1.1.1.1,
      normalizeChain_eq_self m hw.1.1.1.2, normalizeCouple_eq_self q hw.1.1.2]
    exact attachChains_eq_type2 p m q hw.1.2 hw.2
termination_by structural Q

/-- Every well-formed chain code is fixed by normalization. -/
theorem normalizeChain_eq_self (X : RegChain) (hw : X.wf = true) : normalizeChain X = X := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [RegChain.wf, Bool.and_eq_true] at hw
    simp only [normalizeChain, normalizeCouple_eq_self r hw.1.1.1,
      normalizeCouple_eq_self g hw.1.1.2, normalizeChain_eq_self i hw.1.2,
      normalizeChain_eq_self s hw.2]
termination_by structural X
end

/-- Couple normalization is idempotent on all intermediate codes. -/
theorem normalizeCouple_idempotent (Q : RegCpl) :
    normalizeCouple (normalizeCouple Q) = normalizeCouple Q :=
  normalizeCouple_eq_self _ (normalizeCouple_wf Q)

/-- Chain normalization is idempotent on all intermediate codes. -/
theorem normalizeChain_idempotent (X : RegChain) :
    normalizeChain (normalizeChain X) = normalizeChain X :=
  normalizeChain_eq_self _ (normalizeChain_wf X)

end WaveTurbulence.Reg

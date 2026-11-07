/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcDisp3

/-! # P4-W2 (session 13, step 2f): a summand of a bundle vanishes off its order condition

`bundlePtG_eq_zero_of_not_excOrd`: every summand of `bundlePtG` is `if <order condition> then .. else 0` (`tA1 .. tTT`, `rA1 .. rB3`), and `ExcOrd` is that condition
(with the roles of `s₁, t₁` exchanged in case M).  This is the vanishing of the exceptional factor of a record off its exceptional order edges (`hcontract`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13
open scoped ComplexConjugate

open Classical in
theorem bundlePtG_eq_zero_of_not_excOrd (caseA : Prop) {β : Type*} [DecidableEq β] {d : ℕ} (S : SepTerms β d)
    (bs₁ bs₂ rA rB : Finset β) (RQ RT : β → ℝ → ℝ → Mom d → ℂ) (t0 s1 t1 : ℝ) (x y : Mom d)
    (c : Ch S bs₁ bs₂ rA rB) (h : ¬ ExcOrd caseA t0 s1 t1 c) :
    bundlePtG caseA S bs₁ bs₂ rA rB RQ RT t0 s1 t1 x y c = 0 := by
  by_cases hc : caseA
  · rcases c with (c | c | c | c | c | c) | (c | c)
    all_goals first
      | (obtain ⟨c1, c2⟩ := c; rcases c2 with c2 | c2 | c2) | skip
    all_goals
      simp only [ExcOrd, bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_pos hc, tA1, tA2, tKQ, tTQ, tKT, tTT, rA1, rA2, rA3, rB1, rB2, rB3] at h ⊢
      split_ifs at ⊢ <;> simp_all
  · rcases c with (c | c | c | c | c | c) | (c | c)
    all_goals first
      | (obtain ⟨c1, c2⟩ := c; rcases c2 with c2 | c2 | c2) | skip
    all_goals
      simp only [ExcOrd, bundlePtG, ptP, ptR, Sum.elim_inl, Sum.elim_inr, if_neg hc, tA1, tA2, tKQ, tTQ, tKT, tTT, rA1, rA2, rA3, rB1, rB2, rB3] at h ⊢
      split_ifs at ⊢ <;> simp_all


open Classical in
/-- **A kind-2 summand vanishes at equal slots** `s₁ = t₁`: `tTQ`, `tTT` carry the difference `Q(s₁) - Q(t₁)` (resp. `T(t₁) - T(s₁)`). -/
theorem bundlePtG_eq_zero_of_kd2_eq (caseA : Prop) {β : Type*} [DecidableEq β] {d : ℕ} (S : SepTerms β d)
    (bs₁ bs₂ rA rB : Finset β) (RQ RT : β → ℝ → ℝ → Mom d → ℂ) (t0 s : ℝ) (x y : Mom d)
    (c : Ch S bs₁ bs₂ rA rB) (hk : kindOf c = 2) :
    bundlePtG caseA S bs₁ bs₂ rA rB RQ RT t0 s s x y c = 0 := by
  rcases c with (c | c | c | c | c | c) | (c | c)
  all_goals first
    | (exfalso; simp [kindOf] at hk; done)
    | skip
  all_goals
    obtain ⟨c1, c2⟩ := c
    by_cases hc : caseA <;>
    simp [bundlePtG, ptP, tTQ, tTT, hc]

end WaveTurbulence.VineEstS5C.P4.W2

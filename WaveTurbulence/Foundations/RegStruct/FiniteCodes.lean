/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # Finiteness of bounded regular-object structure data (DH21 Corollary 4.9)

The finite-carrier construction is adapted from the audited B2 probe, independently
of all unfinished characterizations.
-/

public section

namespace WaveTurbulence.Reg

theorem chain_size_pos_of_not_isNil {X : RegChain} (h : X.isNil = false) : 2 ≤ X.size := by
  cases X with
  | nil => simp [RegChain.isNil] at h
  | pair => simp only [RegChain.size]; omega

/-- **Finiteness** (for the `finsum` over dominant codes of a given order in B2.1 item 4). -/
theorem finite_wf_codes (N : ℕ) :
    {X : RegChain | X.wf = true ∧ X.size ≤ N}.Finite ∧
      {Q : RegCpl | Q.wf = true ∧ Q.size ≤ N}.Finite := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    -- the couples and chains of size `≤ N - 2`
    have hsmall : N < 2 ∨ ({X : RegChain | X.wf = true ∧ X.size ≤ N - 2}.Finite ∧
        {Q : RegCpl | Q.wf = true ∧ Q.size ≤ N - 2}.Finite) := by
      rcases Nat.lt_or_ge N 2 with h | h
      · exact Or.inl h
      · exact Or.inr (ih (N - 2) (by omega))
    have hC : {X : RegChain | X.wf = true ∧ X.size ≤ N}.Finite := by
      rcases hsmall with h | ⟨hX, hQ⟩
      · refine (Set.finite_singleton RegChain.nil).subset ?_
        rintro (_ | ⟨m, Qr, Qg, inner, rest⟩) ⟨-, hs⟩
        · rfl
        · simp only [RegChain.size] at hs
          omega
      · let f : MiniTreeCode × RegCpl × RegCpl × RegChain × RegChain → RegChain :=
          fun x => .pair x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
        refine ((Set.finite_singleton RegChain.nil).union
          ((Set.finite_univ.prod (hQ.prod (hQ.prod (hX.prod hX)))).image f)).subset ?_
        rintro (_ | ⟨m, Qr, Qg, inner, rest⟩) ⟨hw, hs⟩
        · exact Or.inl rfl
        · right
          simp only [RegChain.wf, Bool.and_eq_true] at hw
          simp only [RegChain.size] at hs
          exact ⟨(m, Qr, Qg, inner, rest), ⟨Set.mem_univ _,
            ⟨hw.1.1.1, (by omega : Qr.size ≤ N - 2)⟩, ⟨hw.1.1.2, (by omega : Qg.size ≤ N - 2)⟩,
            ⟨hw.1.2, (by omega : inner.size ≤ N - 2)⟩, ⟨hw.2, (by omega : rest.size ≤ N - 2)⟩⟩, rfl⟩
    refine ⟨hC, ?_⟩
    rcases hsmall with h | ⟨-, hQ⟩
    · refine (Set.finite_singleton RegCpl.triv).subset ?_
      rintro (_ | ⟨c, Q₁, Q₂, Q₃⟩ | ⟨Xp, Xm, Qlp⟩) ⟨hw, hs⟩
      · rfl
      · simp only [RegCpl.size] at hs
        omega
      · simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
        simp only [RegCpl.size] at hs
        rcases Bool.and_eq_false_iff.1 hw.2 with h1 | h1
        · have := chain_size_pos_of_not_isNil h1
          omega
        · have := chain_size_pos_of_not_isNil h1
          omega
    · let f1 : Fin 2 × RegCpl × RegCpl × RegCpl → RegCpl := fun x => .type1 x.1 x.2.1 x.2.2.1 x.2.2.2
      let f2 : RegChain × RegChain × RegCpl → RegCpl := fun x => .type2 x.1 x.2.1 x.2.2
      refine (((Set.finite_singleton RegCpl.triv).union
        ((Set.finite_univ.prod (hQ.prod (hQ.prod hQ))).image f1)).union
        ((hC.prod (hC.prod hQ)).image f2)).subset ?_
      rintro (_ | ⟨c, Q₁, Q₂, Q₃⟩ | ⟨Xp, Xm, Qlp⟩) ⟨hw, hs⟩
      · exact Or.inl (Or.inl rfl)
      · left; right
        simp only [RegCpl.wf, Bool.and_eq_true] at hw
        simp only [RegCpl.size] at hs
        exact ⟨(c, Q₁, Q₂, Q₃), ⟨Set.mem_univ _, ⟨hw.1.1, (by omega : Q₁.size ≤ N - 2)⟩,
          ⟨hw.1.2, (by omega : Q₂.size ≤ N - 2)⟩, ⟨hw.2, (by omega : Q₃.size ≤ N - 2)⟩⟩, rfl⟩
      · right
        simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
        simp only [RegCpl.size] at hs
        have h2 : 2 ≤ Xp.size + Xm.size := by
          rcases Bool.and_eq_false_iff.1 hw.2 with h1 | h1
          · have := chain_size_pos_of_not_isNil h1
            omega
          · have := chain_size_pos_of_not_isNil h1
            omega
        exact ⟨(Xp, Xm, Qlp), ⟨⟨hw.1.1.1.1, (by omega : Xp.size ≤ N)⟩,
          ⟨hw.1.1.1.2, (by omega : Xm.size ≤ N)⟩, ⟨hw.1.1.2, (by omega : Qlp.size ≤ N - 2)⟩⟩, rfl⟩


end WaveTurbulence.Reg

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeEval

/-! # A marked non-special chosen node annihilates the actual limit coefficient

This completes the zero branch needed in DH23 Proposition 6.1. It uses
the actual cancellation recursion and places no coefficient identity in
the hypotheses.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open TTree Reg ClassJR Links Cancel Set

mutual
/-- A marked chosen node outside the source special candidates forces zero. -/
theorem cplJ_eq_zero_of_nonspecial (Z : Finset Addr) (z : Addr) (hz : z ∈ Z) :
    ∀ (Q : RegCpl) (a b : Addr), z ∈ chosenSet (Q.linksAt a b) →
      z ∉ cplSpecial Q a b →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, cplJ Z Q a b t s = 0
  | .triv, _, _, hc, _, _, _, _, _ => by simp [RegCpl.linksAt,chosenSet] at hc
  | .type1 c Q₁ Q₂ Q₃, a, b, hc, hn, t, ht, s, hs => by
    simp only [cplJ]
    split_ifs with ha
    · rfl
    · have hn1 : z ∉ cplSpecial Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) :=
        fun h => hn (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))
      have hn2 : z ∉ cplSpecial Q₂ (addrExt b [1]) (addrExt a [1]) :=
        fun h => hn (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
      have hn3 : z ∉ cplSpecial Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) :=
        fun h => hn (List.mem_append.mpr (Or.inr h))
      simp only [RegCpl.linksAt,chosenSet_cons,chosenSet_append,
        Finset.mem_insert,Finset.mem_union] at hc
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) fun τ hτ => ?_]
      · simp
      · rw [uIcc_of_le (le_min ht.1 hs.1)] at hτ
        have hτ' : τ ∈ Icc (0:ℝ) 1 := ⟨hτ.1,hτ.2.trans ((min_le_left _ _).trans ht.2)⟩
        simp only
        rcases hc with he | ((h1 | h2) | h3)
        · exact False.elim (ha (he ▸ hz))
        · rw [cplJ_eq_zero_of_nonspecial Z z hz Q₁ _ _ h1 hn1 τ hτ' τ hτ']; ring
        · rw [cplJ_eq_zero_of_nonspecial Z z hz Q₂ _ _ h2 hn2 τ hτ' τ hτ']; ring
        · rw [cplJ_eq_zero_of_nonspecial Z z hz Q₃ _ _ h3 hn3 τ hτ' τ hτ']; ring
  | .type2 Xp Xm Qlp, a, b, hc, hn, t, ht, s, hs => by
    have hnp : z ∉ chainSpecial Xp 1 a :=
      fun h => hn (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))
    have hnm : z ∉ chainSpecial Xm (-1) b :=
      fun h => hn (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
    have hnl : z ∉ cplSpecial Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) :=
      fun h => hn (List.mem_append.mpr (Or.inr h))
    simp only [RegCpl.linksAt,chosenSet_append,Finset.mem_union] at hc
    simp only [cplJ]
    rcases hc with (hp | hm) | hl
    · exact chainJ_eq_zero_of_nonspecial Z z hz Xp 1 a hp hnp t ht _
    · exact chainJ_zero_cont Z Xp 1 a t ht _ fun _ _ =>
        chainJ_eq_zero_of_nonspecial Z z hz Xm (-1) b hm hnm s hs _
    · exact chainJ_zero_cont Z Xp 1 a t ht _ fun t' ht' =>
        chainJ_zero_cont Z Xm (-1) b s hs _ fun s' hs' =>
          cplJ_eq_zero_of_nonspecial Z z hz Qlp _ _ hl hnl t' ht' s' hs'

/-- The same zero statement for a chain, uniformly over its continuation. -/
theorem chainJ_eq_zero_of_nonspecial (Z : Finset Addr) (z : Addr) (hz : z ∈ Z) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr), z ∈ chosenSet (X.linksAt ζ a) →
      z ∉ chainSpecial X ζ a →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ g : ℝ → ℂ, chainJ Z X ζ a t g = 0
  | .nil, _, _, hc, _, _, _, _ => by simp [RegChain.linksAt,chosenSet] at hc
  | .pair m Qr Qg .nil r, ζ, a, hc, hn, t, ht, g => by
    rw [chainSpecial_pair] at hn
    have hnr : z ∉ cplSpecial Qr (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2 :=
      fun h => hn (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))))))
    have hng : z ∉ cplSpecial Qg (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2 :=
      fun h => hn (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))))))
    have hnrest : z ∉ chainSpecial r (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) :=
      fun h => hn (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h))))
    have hza : z ≠ a := by
      intro he
      apply hn
      apply List.mem_append.mpr
      exact Or.inl (by simpa only [RegChain.isNil,ite_true,List.mem_singleton] using he)
    rw [linksAt_pair] at hc
    simp only [RegChain.linksAt,chosenSet_cons,chosenSet_append,
      chosenSet_nil,Finset.union_empty,
      Finset.mem_insert,Finset.mem_union] at hc
    simp only [chainJ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) fun τ hτ => ?_]
    · simp
    · rw [uIcc_of_le ht.1] at hτ
      have hτ' : τ ∈ Icc (0:ℝ) 1 := ⟨hτ.1,hτ.2.trans ht.2⟩
      simp only
      rcases hc with he | ((hr | hg) | hrest)
      · exact False.elim (hza he)
      · rw [cplJ_eq_zero_of_nonspecial Z z hz Qr _ _ hr hnr τ hτ' τ hτ']; ring
      · rw [cplJ_eq_zero_of_nonspecial Z z hz Qg _ _ hg hng τ hτ' τ hτ']; ring
      · rw [chainJ_eq_zero_of_nonspecial Z z hz r _ _ hrest hnrest τ hτ' g]; ring
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, _, _, _, _, _ => rfl
end

end WaveTurbulence.RegAsymp

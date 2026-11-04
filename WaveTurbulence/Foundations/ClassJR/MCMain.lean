/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCCodesVars

/-!
# DH21 Proposition 5.1 for codes of regular couples

By induction on the code (DH21 L944–L946, "the proof is done by induction, using the recursive
description in (newexp1) and (newexp2)"), `B̃_Q` has the expansion (maincoef3) with the DH23 weights
in the chosen nodes `𝒩^ch` (`RegCpl.mcexp`); the pair coefficients of the chains have it in the
variables of their two couples (`RegChain.mcexp_coef`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Disj

/-- Two disjoint subtrees contain disjoint sets of addresses. -/
theorem disjoint_of_sub {A B : Finset Addr} {S T : Set Addr} (hA : (↑A : Set Addr) ⊆ S)
    (hB : (↑B : Set Addr) ⊆ T) (hST : Disjoint S T) : Disjoint A B :=
  Finset.disjoint_coe.1 (hST.mono hA hB)

/-- The two couples of a chain pair have disjoint variables. -/
theorem pair_couples_disjoint (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ)
    (x : Addr) :
    Disjoint (chosenSet (if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt x [m.red.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt x [m.red.1])))
    (chosenSet (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt x [m.green.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt x [m.green.1]))) := by
  have hk : ∀ k : Fin 3, addrExt x ([m.c] ++ inner.lonePath ++ [k]) =
      addrExt (addrExt x (m.c :: inner.lonePath)) [k] := fun k => by
    rw [addrExt_addrExt]; simp
  have hsub : ∀ (Q : RegCpl) (i k : Fin 3) (bb : Bool),
      (↑(chosenSet (if bb then Q.linksAt (addrExt x [i]) (addrExt x ([m.c] ++ inner.lonePath ++ [k]))
        else Q.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [k])) (addrExt x [i]))) : Set Addr) ⊆
        Up (addrExt x [i]) ∪ Up (addrExt (addrExt x (m.c :: inner.lonePath)) [k]) := by
    intro Q i k bb
    cases bb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hk, Set.union_comm]; exact RegCpl.chosen_sub Q _ _
    · simp only [↓reduceIte]
      rw [hk]; exact RegCpl.chosen_sub Q _ _
  have h1 := hsub Qr m.red.1 m.red.2 (decide (slotSign ζ m.red.1 = 1))
  have h2 := hsub Qg m.green.1 m.green.2 (decide (slotSign ζ m.green.1 = 1))
  simp only [decide_eq_true_eq] at h1 h2
  refine Finset.disjoint_coe.1 (Disjoint.mono h1 h2 ?_)
  have hnb : Up (addrExt (addrExt x (m.c :: inner.lonePath)) [m.green.2]) ⊆ Up (addrExt x (m.c :: inner.lonePath)) :=
    up_addrExt_subset _ _
  have hnb' : Up (addrExt (addrExt x (m.c :: inner.lonePath)) [m.red.2]) ⊆ Up (addrExt x (m.c :: inner.lonePath)) :=
    up_addrExt_subset _ _
  refine Disjoint.union_left (Disjoint.union_right ?_ ?_) (Disjoint.union_right ?_ ?_)
  · exact disjoint_up_cons x m.red_fst_ne_green_fst [] []
  · exact (disjoint_up_cons x m.red_fst_ne_c [] inner.lonePath).mono_right hnb
  · exact (disjoint_up_cons x m.green_fst_ne_c [] inner.lonePath).symm.mono_left hnb'
  · exact disjoint_up_cons _ m.red_snd_ne_green_snd [] []

end Disj

section Main

variable {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b) (hab1 : a + b < 1)
  (hab : a + b ≤ θ) (hA : A1 ≤ A)
include hθ0 hθ1 ha hb hab1 hab hA

-- The linter does not see the section hypotheses used through the recursive calls of the block.
set_option linter.unusedSectionVars false in
mutual
/-- **DH21 Proposition 5.1 for a couple code** (with the DH23 weights): `B̃_Q` has the expansion
(maincoef3) in its chosen nodes, with the constant `Q.NB θ a b` of the recursion. -/
theorem RegCpl.mcexp : ∀ (Q : RegCpl) (x y : Addr), Disjoint (Up x) (Up y) →
    MCExp θ a b A (Q.NB θ a b) nodeSgn (chosenSet (Q.linksAt x y)) (Q.Bt x y)
  | .triv, x, y, _ => by
    simpa [RegCpl.linksAt, chosenSet_nil, RegCpl.NB, RegCpl.Bt] using
      MCExp.one (V := Addr) (a := a) (b := b) (A := A) nodeSgn hθ0 hθ1.le
  | .type1 c Q₁ Q₂ Q₃, x, y, hxy => by
    have h₁ := RegCpl.mcexp Q₁ (addrExt x [0]) (addrExt y [c.partner 0]) (disjoint_up_ext hxy _ _)
    have h₂ := RegCpl.mcexp Q₂ (addrExt y [1]) (addrExt x [1]) (disjoint_up_ext hxy.symm _ _)
    have h₃ := RegCpl.mcexp Q₃ (addrExt x [2]) (addrExt y [c.partner 2]) (disjoint_up_ext hxy _ _)
    have r₁ := RegCpl.chosen_sub Q₁ (addrExt x [0]) (addrExt y [c.partner 0])
    have r₂ := RegCpl.chosen_sub Q₂ (addrExt y [1]) (addrExt x [1])
    have r₃ := RegCpl.chosen_sub Q₃ (addrExt x [2]) (addrExt y [c.partner 2])
    have hxy' : ∀ (p q : Path), Disjoint (Up (addrExt x p)) (Up (addrExt y q)) :=
      disjoint_up_ext hxy
    have h12 := disjoint_of_sub r₁ r₂ (Disjoint.union_left
      (Disjoint.union_right (hxy' _ _) (disjoint_up_cons x (i := 0) (j := 1) (by decide) [] []))
      (Disjoint.union_right (disjoint_up_cons y c.partner_zero_ne_one [] []) (hxy' _ _).symm))
    have h13 := disjoint_of_sub r₁ r₃ (Disjoint.union_left
      (Disjoint.union_right (disjoint_up_cons x (i := 0) (j := 2) (by decide) [] []) (hxy' _ _))
      (Disjoint.union_right (hxy' _ _).symm (disjoint_up_cons y c.partner_zero_ne_two [] [])))
    have h23 := disjoint_of_sub r₂ r₃ (Disjoint.union_left
      (Disjoint.union_right (hxy' _ _).symm (disjoint_up_cons y c.partner_two_ne_one.symm [] []))
      (Disjoint.union_right (disjoint_up_cons x (i := 1) (j := 2) (by decide) [] []) (hxy' _ _)))
    have hx : ∀ (i : Fin 3) (j : Fin 3), x ∉ Up (addrExt x [i]) ∪ Up (addrExt y [j]) := by
      intro i j h
      rcases h with h | h
      · exact notMem_up_cons x i [] h
      · exact Set.disjoint_left.1 hxy (self_mem_up x) (up_addrExt_subset _ _ h)
    have hv : x ∉ chosenSet (Q₁.linksAt (addrExt x [0]) (addrExt y [c.partner 0])) ∪
        chosenSet (Q₂.linksAt (addrExt y [1]) (addrExt x [1])) ∪
        chosenSet (Q₃.linksAt (addrExt x [2]) (addrExt y [c.partner 2])) := by
      simp only [Finset.mem_union, not_or]
      refine ⟨⟨fun h => hx 0 _ (r₁ h), fun h => ?_⟩, fun h => hx 2 _ (r₃ h)⟩
      have := r₂ h
      rw [Set.union_comm] at this
      exact hx 1 1 this
    have key := MCExp.type1 (F := ![Q₁.Bt (addrExt x [0]) (addrExt y [c.partner 0]),
        Q₂.Bt (addrExt y [1]) (addrExt x [1]), Q₃.Bt (addrExt x [2]) (addrExt y [c.partner 2])])
      h₁ h₂ h₃ h12 h13 h23 hv hθ0 hθ1 ha.le hb hab1 (by linarith) hA ![false, true, false]
    simpa [RegCpl.linksAt, chosenSet_cons, chosenSet_append, RegCpl.NB, RegCpl.Bt] using key
  | .type2 Xp Xm Qlp, x, y, hxy => by
    have hp := Xp.chainFacts 1 x 0
    have hm := Xm.chainFacts (-1) y 0
    have hlp := RegCpl.mcexp Qlp (addrExt x Xp.lonePath) (addrExt y Xm.lonePath)
      (disjoint_up_ext hxy _ _)
    have rlp := RegCpl.chosen_sub Qlp (addrExt x Xp.lonePath) (addrExt y Xm.lonePath)
    -- the regions
    have hlx : Up (addrExt x Xp.lonePath) ⊆ Up x := up_addrExt_subset _ _
    have hly : Up (addrExt y Xm.lonePath) ⊆ Up y := up_addrExt_subset _ _
    have hvm : (↑(varsMinus (Xm.sigmaAt y 0) Xm.code (Xm.varsAt (-1) y 0)
        (chosenSet (Qlp.linksAt (addrExt x Xp.lonePath) (addrExt y Xm.lonePath)))) : Set Addr) ⊆
        Up y ∪ Up (addrExt x Xp.lonePath) := by
      intro v hv
      simp only [varsMinus, Finset.coe_union, Set.mem_union, Finset.mem_coe, unionS,
        Finset.mem_biUnion, Finset.mem_image] at hv
      rcases hv with (⟨j, hj, hv⟩ | hv) | ⟨j, hj, rfl⟩
      · exact Or.inl ((hm.vars_sub j (by simpa [Finset.mem_Ico] using hj)) hv).1
      · rcases rlp hv with h | h
        · exact Or.inr h
        · exact Or.inl (hly h)
      · exact Or.inl (hm.sig_mem j (by simpa [Finset.mem_Ico] using hj)).1
    have hdx : Disjoint (Up x \ Up (addrExt x Xp.lonePath)) (Up y ∪ Up (addrExt x Xp.lonePath)) :=
      Disjoint.union_right (hxy.mono_left Set.sdiff_subset) Set.disjoint_sdiff_left
    have hdy : Disjoint (Up y \ Up (addrExt y Xm.lonePath))
        (Up (addrExt x Xp.lonePath) ∪ Up (addrExt y Xm.lonePath)) :=
      Disjoint.union_right ((hxy.symm.mono_left Set.sdiff_subset).mono_right hlx)
        Set.disjoint_sdiff_left
    have key := MCExp.type2 hθ0 hθ1 ha hb hab1 hab hA (ζ := nodeSgn) (σp := Xp.sigmaAt x 0)
      (εp := fun j => nodeSgn (Xp.sigmaAt x 0 j)) (fun j => nodeSgn_eq _) (cp := Xp.code)
      (fun j _ => rfl) (by simpa using hp.inj) (Sp := Xp.varsAt 1 x 0)
      (Np := Xp.NBAt θ a b 0) (Fp := Xp.coefAt 1 x 0)
      (fun j hj => RegChain.mcexp_coef Xp 1 x 0 j (by simpa using hj))
      (σm := Xm.sigmaAt y 0) (εm := fun j => nodeSgn (Xm.sigmaAt y 0 j)) (fun j => nodeSgn_eq _)
      (cm := Xm.code) (fun j _ => rfl) (by simpa using hm.inj) (Sm := Xm.varsAt (-1) y 0)
      (Nm := Xm.NBAt θ a b 0) (Fm := Xm.coefAt (-1) y 0)
      (fun j hj => RegChain.mcexp_coef Xm (-1) y 0 j (by simpa using hj)) hlp
      (fun j hj k hk hjk => hm.disj j (by simpa using hj) k (by simpa using hk) hjk)
      (fun j hj => disjoint_of_sub (hm.vars_sub j (by simpa using hj)) rlp hdy)
      (fun j hj k hk => hm.sig_notMem j (by simpa using hj) k (by simpa using hk))
      (fun k hk h => Set.disjoint_left.1 hdy (hm.sig_mem k (by simpa using hk)) (rlp h))
      (fun j hj k hk hjk => hp.disj j (by simpa using hj) k (by simpa using hk) hjk)
      (fun j hj => disjoint_of_sub (hp.vars_sub j (by simpa using hj)) hvm hdx)
      (fun j hj k hk => hp.sig_notMem j (by simpa using hj) k (by simpa using hk))
      (fun k hk h => Set.disjoint_left.1 hdx (hp.sig_mem k (by simpa using hk)) (hvm h))
    have e : chosenSet ((RegCpl.type2 Xp Xm Qlp).linksAt x y) =
        unionS (Xp.varsAt 1 x 0) 0 Xp.code.size ∪
          varsMinus (Xm.sigmaAt y 0) Xm.code (Xm.varsAt (-1) y 0)
            (chosenSet (Qlp.linksAt (addrExt x Xp.lonePath) (addrExt y Xm.lonePath))) ∪
          (Finset.Ico 0 Xp.code.size).image (Xp.sigmaAt x 0) := by
      simp only [RegCpl.linksAt, chosenSet_append]
      rw [hp.chosen, hm.chosen]
      simp only [varsMinus, zero_add]
      ext v
      simp only [Finset.mem_union]
      tauto
    rw [e]
    exact key

/-- **The pair coefficients of a chain** have the expansion (maincoef3) in the variables of their
two couples. -/
theorem RegChain.mcexp_coef : ∀ (X : RegChain) (ζ : ℤˣ) (x : Addr) (q : ℕ),
    ∀ j ∈ Set.Ico q (q + X.code.size),
      MCExp θ a b A (X.NBAt θ a b q j) nodeSgn (X.varsAt ζ x q j) (X.coefAt ζ x q j)
  | .nil, _, _, _, j, hj => by simp [RegChain.code, LegalCode.size] at hj
  | .pair m Qr Qg inner rest, ζ, x, q, j, hj => by
    rcases mem_Ico_pair m Qr Qg inner rest q hj with rfl | hj' | hj'
    · have hA0 : 0 ≤ A := A1_nonneg.trans hA
      have hk : ∀ k : Fin 3, addrExt x ([m.c] ++ inner.lonePath ++ [k]) =
          addrExt x (m.c :: (inner.lonePath ++ [k])) := fun k => by simp [addrExt]
      have hcpl : ∀ (Q : RegCpl), (∀ u v, Disjoint (Up u) (Up v) →
          MCExp θ a b A (Q.NB θ a b) nodeSgn (chosenSet (Q.linksAt u v)) (Q.Bt u v)) →
          ∀ (i k : Fin 3), i ≠ m.c → ∀ bb : Bool,
          MCExp θ a b A (Q.NB θ a b) nodeSgn
            (chosenSet (if bb then Q.linksAt (addrExt x [i]) (addrExt x ([m.c] ++ inner.lonePath ++ [k]))
              else Q.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [k])) (addrExt x [i])))
            (fun α ta tb => if bb then Q.Bt (addrExt x [i]) (addrExt x ([m.c] ++ inner.lonePath ++ [k])) α ta tb
              else Q.Bt (addrExt x ([m.c] ++ inner.lonePath ++ [k])) (addrExt x [i]) α tb ta) := by
        intro Q hQ i k hi bb
        have huv : Disjoint (Up (addrExt x [i])) (Up (addrExt x ([m.c] ++ inner.lonePath ++ [k]))) := by
          rw [hk]; exact disjoint_up_cons x hi [] _
        cases bb
        · simpa [swapT] using (hQ _ _ huv.symm).swapTimes true
        · simpa using hQ _ _ huv
      have h1 := hcpl Qr (RegCpl.mcexp Qr) m.red.1 m.red.2 m.red_fst_ne_c
        (decide (slotSign ζ m.red.1 = 1))
      have h2 := hcpl Qg (RegCpl.mcexp Qg) m.green.1 m.green.2 m.green_fst_ne_c
        (decide (slotSign ζ m.green.1 = 1))
      simp only [decide_eq_true_eq] at h1 h2
      have key := MCExp.mul h1 h2 (pair_couples_disjoint m Qr Qg inner ζ x) hθ0 ha.le
        (by linarith) hA0
      rw [NBAt_pair_self, varsAt_pair_self]
      refine key.congr fun α t s _ _ => ?_
      simp only [RegChain.coefAt, ↓reduceIte]
    · rw [NBAt_pair_inner _ _ _ _ _ _ _ _ _ hj', varsAt_pair_inner _ _ _ _ _ _ _ _ hj',
        coefAt_pair_inner _ _ _ _ _ _ _ _ hj']
      exact RegChain.mcexp_coef inner _ _ _ j hj'
    · rw [NBAt_pair_rest _ _ _ _ _ _ _ _ _ hj', varsAt_pair_rest _ _ _ _ _ _ _ _ hj',
        coefAt_pair_rest _ _ _ _ _ _ _ _ hj']
      exact RegChain.mcexp_coef rest _ _ _ j hj'
end

end Main

end WaveTurbulence.ClassJR

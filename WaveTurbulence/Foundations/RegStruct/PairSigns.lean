/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.AddressSigns

/-! # Every decoded pair is oriented from positive to negative (DH21 Propositions 4.7–4.8) -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Straight and crossed mini-couple matchings preserve the child slot sign. -/
theorem slotSign_partner (c : MiniCplCode) (ζ : ℤˣ) (j : Fin 3) :
    slotSign ζ (c.partner j) = slotSign ζ j := by
  fin_cases c <;> fin_cases j <;> simp [MiniCplCode.partner, slotSign]

mutual
/-- Every listed couple pair starts at a positive leaf and ends at a negative leaf. -/
theorem couple_pairsAt_signs {w : ℕ} (Q : RegCpl) (σ : Fin w → ℤˣ)
    (a b : Fin w × Path) (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1)
    (z : (Fin w × Path) × (Fin w × Path)) (hz : z ∈ Q.pairsAt a b) :
    nodeSign σ z.1 = 1 ∧ nodeSign σ z.2 = -1 := by
  cases Q with
  | triv =>
    have he := List.mem_singleton.mp hz
    subst z
    exact ⟨ha,hb⟩
  | type1 c r g d =>
    simp only [RegCpl.pairsAt, List.mem_append] at hz
    rcases hz with (hr | hg) | hd
    · exact couple_pairsAt_signs r σ _ _
        (by simp [nodeSign_step,ha,slotSign])
        (by rw [nodeSign_step,slotSign_partner,hb]; rfl) z hr
    · exact couple_pairsAt_signs g σ _ _
        (by simp [nodeSign_step,hb,slotSign])
        (by simp [nodeSign_step,ha,slotSign]) z hg
    · exact couple_pairsAt_signs d σ _ _
        (by simp [nodeSign_step,ha,slotSign])
        (by rw [nodeSign_step,slotSign_partner,hb]; rfl) z hd
  | type2 p m q =>
    simp only [RegCpl.pairsAt, List.mem_append] at hz
    rcases hz with (hp | hm) | hq
    · exact chain_pairsAt_signs p σ 1 a ha z hp
    · exact chain_pairsAt_signs m σ (-1) b hb z hm
    · exact couple_pairsAt_signs q σ _ _
        ((nodeSign_spine σ a p).trans ha) ((nodeSign_spine σ b m).trans hb) z hq
termination_by structural Q

/-- Every side-couple pair in a chain has the source's positive/negative orientation. -/
theorem chain_pairsAt_signs {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ) (ζ : ℤˣ)
    (a : Fin w × Path) (ha : nodeSign σ a = ζ)
    (z : (Fin w × Path) × (Fin w × Path)) (hz : z ∈ X.pairsAt ζ a) :
    nodeSign σ z.1 = 1 ∧ nodeSign σ z.2 = -1 := by
  cases X with
  | nil => simp only [RegChain.pairsAt, List.not_mem_nil] at hz
  | pair m r g i s =>
    simp only [RegChain.pairsAt, List.mem_append] at hz
    rcases hz with ((hr | hg) | hi) | hs
    · have hfront : nodeSign σ (addrExt a [m.red.1]) = slotSign ζ m.red.1 := by
        rw [nodeSign_step,ha]
      have hback : nodeSign σ (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])) =
          -slotSign ζ m.red.1 := by rw [nodeSign_chain_child,ha,slotSign_red]
      by_cases hp : slotSign ζ m.red.1 = 1
      · simp only [hp,ite_true] at hr
        exact couple_pairsAt_signs r σ _ _ (hfront.trans hp)
          (hback.trans (congrArg Neg.neg hp)) z hr
      · have hm : slotSign ζ m.red.1 = -1 := (Int.units_eq_one_or _).resolve_left hp
        simp only [hp,ite_false] at hr
        exact couple_pairsAt_signs r σ _ _ (by rw [hback,hm,neg_neg]) (hfront.trans hm) z hr
    · have hfront : nodeSign σ (addrExt a [m.green.1]) = slotSign ζ m.green.1 := by
        rw [nodeSign_step,ha]
      have hback : nodeSign σ (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])) =
          -slotSign ζ m.green.1 := by rw [nodeSign_chain_child,ha,slotSign_green]
      by_cases hp : slotSign ζ m.green.1 = 1
      · simp only [hp,ite_true] at hg
        exact couple_pairsAt_signs g σ _ _ (hfront.trans hp)
          (hback.trans (congrArg Neg.neg hp)) z hg
      · have hm : slotSign ζ m.green.1 = -1 := (Int.units_eq_one_or _).resolve_left hp
        simp only [hp,ite_false] at hg
        exact couple_pairsAt_signs g σ _ _ (by rw [hback,hm,neg_neg]) (hfront.trans hm) z hg
    · exact chain_pairsAt_signs i σ _ _ (by rw [nodeSign_step,ha]) z hi
    · exact chain_pairsAt_signs s σ _ _ (by rw [nodeSign_chain_child,ha]) z hs
termination_by structural X
end

end WaveTurbulence.Reg

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeNodes
public import WaveTurbulence.Foundations.RegStruct.InsertMiniTree

/-! # Code operation B leaves unrepresented addresses unchanged -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

mutual
/-- A B-step outside a represented couple changes none of its code data. -/
theorem insertMiniCouple_outside {w : ℕ} (Q : RegCpl) (a b target : Fin w × Path)
    (m : MiniTreeCode) (h : target ∉ coupleNodes Q a b) :
    insertMiniCouple Q a b target m = Q := by
  have ha : target ≠ a := by
    intro he
    apply h
    rw [he]
    exact coupleNodes_left_mem Q a b
  have hb : target ≠ b := by
    intro he
    apply h
    rw [he]
    exact coupleNodes_right_mem Q a b
  cases Q with
  | triv => rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  | type1 c r g d =>
    simp only [coupleNodes,Finset.mem_union,not_or] at h
    rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
    dsimp only
    rw [insertMiniCouple_outside r _ _ target m h.1.1.2,
      insertMiniCouple_outside g _ _ target m h.1.2,
      insertMiniCouple_outside d _ _ target m h.2]
  | type2 p n q =>
    simp only [coupleNodes,Finset.mem_union,not_or] at h
    rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
    dsimp only
    rw [insertMiniChain_outside p _ _ target m h.1.1,
      insertMiniChain_outside n _ _ target m h.1.2,
      insertMiniCouple_outside q _ _ target m h.2]
termination_by structural Q

/-- An empty chain or a B-step outside a chain's represented nodes leaves it unchanged. -/
theorem insertMiniChain_outside {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a target : Fin w × Path)
    (m : MiniTreeCode) (h : target ∉ chainNodes X ζ a) :
    insertMiniChain X ζ a target m = X := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    simp only [chainNodes,Finset.mem_union,not_or] at h
    have hroots := h.1.1.1.1
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hroots
    have hRset := h.1.1.1.2
    have hGset := h.1.1.2
    have hR : (if slotSign ζ k.red.1 = 1 then
        insertMiniCouple r (addrExt a [k.red.1])
          (addrExt a ([k.c] ++ i.lonePath ++ [k.red.2])) target m
      else insertMiniCouple r (addrExt a ([k.c] ++ i.lonePath ++ [k.red.2]))
        (addrExt a [k.red.1]) target m) = r := by
      by_cases hr : slotSign ζ k.red.1 = 1
      · simp only [hr,ite_true] at hRset ⊢
        exact insertMiniCouple_outside r _ _ target m hRset
      · simp only [hr,ite_false] at hRset ⊢
        exact insertMiniCouple_outside r _ _ target m hRset
    have hG : (if slotSign ζ k.green.1 = 1 then
        insertMiniCouple g (addrExt a [k.green.1])
          (addrExt a ([k.c] ++ i.lonePath ++ [k.green.2])) target m
      else insertMiniCouple g (addrExt a ([k.c] ++ i.lonePath ++ [k.green.2]))
        (addrExt a [k.green.1]) target m) = g := by
      by_cases hg : slotSign ζ k.green.1 = 1
      · simp only [hg,ite_true] at hGset ⊢
        exact insertMiniCouple_outside g _ _ target m hGset
      · simp only [hg,ite_false] at hGset ⊢
        exact insertMiniCouple_outside g _ _ target m hGset
    rw [insertMiniChain,ite_eq_right hroots.1,ite_eq_right hroots.2,hR,hG,
      insertMiniChain_outside i _ _ target m h.1.2,
      insertMiniChain_outside s _ _ target m h.2]
termination_by structural X
end

end WaveTurbulence.Reg

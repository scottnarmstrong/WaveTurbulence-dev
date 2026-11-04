/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OffSpineSeparation

/-! # Recovering each chain pair's lower node from its actual red-side pairing -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The red front slot depends only on the first continuation slot. -/
theorem miniTree_red_front_of_c (k l : MiniTreeCode) (h : k.c = l.c) : k.red.1 = l.red.1 := by
  obtain ⟨c,b⟩ := k
  obtain ⟨c',b'⟩ := l
  change c = c' at h
  subst c'
  fin_cases c <;> fin_cases b <;> fin_cases b' <;> simp [MiniTreeCode.red]

/-- The source table is recovered from its two continuation slots and red back slot. -/
theorem miniTree_eq_of_slots (k l : MiniTreeCode) (hc : k.c = l.c)
    (hl : k.lone = l.lone) (hr : k.red.2 = l.red.2) : k = l := by
  obtain ⟨c,b⟩ := k
  obtain ⟨c',b'⟩ := l
  change c = c' at hc
  subst c'
  fin_cases c <;> fin_cases b <;> fin_cases b' <;> simp_all [MiniTreeCode.lone,MiniTreeCode.red]

/-- Equal actual spines and side pairings recover the outer mini-code and its inner/rest split. -/
theorem chain_pair_addresses_unique (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k l : MiniTreeCode) (r g r' g' : RegCpl) (i s i' s' : RegChain)
    (ζ : ℤˣ) (h h' : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (ha' : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair l r' g' i' s').plug ζ h'))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2)
    (hP' : ∀ p ∈ (RegChain.pair l r' g' i' s').pairsAt ζ a, p ∈ Q.raw.2)
    (hpath : (RegChain.pair k r g i s).lonePath = (RegChain.pair l r' g' i' s').lonePath) :
    k = l ∧ i.lonePath = i'.lonePath ∧ s.lonePath = s'.lonePath := by
  have hlist := hpath
  simp only [RegChain.lonePath,List.cons_append] at hlist
  have hc : k.c = l.c := (List.cons.inj hlist).1
  have hfront := miniTree_red_front_of_c k l hc
  have hx := chain_back_offSpine k r g i s k.red.2 (miniTree_slots_separate k).2.2.2.1
  have hy := chain_back_offSpine l r' g' i' s' l.red.2 (miniTree_slots_separate l).2.2.2.1
  rw [← hpath] at hy
  have hrX := subCoupleAt_physical G _ _ _ (chain_red_subCoupleAt Q G hG a k r g i s ζ h ha hP)
  have hrY := subCoupleAt_physical G _ _ _ (chain_red_subCoupleAt Q G hG a l r' g' i' s' ζ h' ha' hP')
  rw [← hfront] at hrY
  have hback := SubCoupleAt.partner_unique_offSpine a _ hx hy hrX hrY
  have hp := congrArg (fun z : Fin 2 × Path => z.2) hback
  have hrel : ([k.c] ++ i.lonePath) ++ [k.red.2] = ([l.c] ++ i'.lonePath) ++ [l.red.2] :=
    List.append_cancel_left hp
  have hsecond := congrArg List.dropLast hrel
  simp only [List.dropLast_concat] at hsecond
  have hi : i.lonePath = i'.lonePath := (List.cons.inj (by
    simpa only [List.singleton_append] using hsecond)).2
  have hred : k.red.2 = l.red.2 := by
    rw [hsecond] at hrel
    exact (List.cons.inj (List.append_cancel_left hrel)).1
  have htail := (List.cons.inj hlist).2
  rw [hi] at htail
  simp only [List.append_assoc,List.singleton_append] at htail
  have hlast := List.cons.inj (List.append_cancel_left htail)
  exact ⟨miniTree_eq_of_slots k l hc hlast.1 hred,hi,hlast.2⟩

end WaveTurbulence.Reg

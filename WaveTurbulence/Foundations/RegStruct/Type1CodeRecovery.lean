/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type1SubCouples

/-! # Recovering the mini-couple code from the actual leaf pairing -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The first positive child distinguishes the two source mini-couple pairings. -/
theorem miniCouple_eq_of_first_partner (c d : MiniCplCode) (h : c.partner 0 = d.partner 0) : c = d := by
  fin_cases c <;> fin_cases d <;> simp_all [MiniCplCode.partner]

/-- Equality of decoded type-1 carriers forces equality of their mini-couple code.
The proof uses actual closed sub-couples and a cross-root leaf witness. -/
theorem type1_miniCode_unique (c d : MiniCplCode) (r g b r' g' b' : RegCpl)
    (he : decodedCouple (.type1 c r g b) = decodedCouple (.type1 d r' g' b')) : c = d := by
  apply miniCouple_eq_of_first_partner
  by_contra hne
  let G := decodedCouple (.type1 c r g b)
  let A := type1FirstNode c r g b 0
  let B := type1SecondNode c r g b 0
  have hC : ((1 : Fin 2),[d.partner 0]).2 ∈ (G.tree (1 : Fin 2)).nodes := by
    have hv := (type1SecondNode d r' g' b' 0).2
    change [d.partner 0] ∈ ((decodedCouple (.type1 d r' g' b')).tree 1).nodes at hv
    change [d.partner 0] ∈ ((decodedCouple (.type1 c r g b)).tree 1).nodes
    rw [he]
    exact hv
  let C : GNode G.tree := ⟨(1,[d.partner 0]),hC⟩
  have hAC : Comb.IsSubCouple G A C := by
    have ht : ∀ a b : GNode G.tree,
        a.1 = (type1Frame d 0).1 → b.1 = (type1Frame d 0).2 → Comb.IsSubCouple G a b := by
      change ∀ a' b' : GNode (decodedCouple (.type1 c r g b)).tree,
        a'.1 = (type1Frame d 0).1 → b'.1 = (type1Frame d 0).2 →
        Comb.IsSubCouple (decodedCouple (.type1 c r g b)) a' b'
      rw [he]
      intro a b ha hb
      have hea : a = type1FirstNode d r' g' b' 0 := Subtype.ext ha
      have heb : b = type1SecondNode d r' g' b' 0 := Subtype.ext hb
      rw [hea,heb]
      exact type1_side_subCouple d r' g' b' 0
    exact ht A C rfl rfl
  have hBC : B.Incomparable C := by
    have ht := incomp_distinct_children ((1 : Fin 2),[]) (c.partner 0) (d.partner 0) [] [] hne
    constructor
    · intro hh
      apply ht.1
      exact ⟨hh.1.symm,hh.2⟩
    · intro hh
      apply ht.2
      exact ⟨hh.1.symm,hh.2⟩
  exact no_incomparable_partner_roots (type1_side_subCouple c r g b 0) hAC hBC

end WaveTurbulence.Reg

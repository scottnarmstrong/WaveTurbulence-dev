/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.RawPairRecovery

/-! # Distinct off-spine child roots are incomparable -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- A first departure from a fixed path: its parent is on the path but it is not. -/
def OffSpine (p x : Path) : Prop := ¬ x <+: p ∧ x.dropLast <+: p

/-- Two distinct first departures cannot be ancestors of one another. -/
theorem OffSpine.not_prefix {p x y : Path} (hx : OffSpine p x) (hy : OffSpine p y)
    (hne : x ≠ y) : ¬ x <+: y := by
  intro hxy
  have hlt : x.length < y.length := by
    have hle := hxy.length_le
    by_contra hn
    exact hne (hxy.eq_of_length_le (by omega))
  have hlen : x.length ≤ y.dropLast.length := by rw [List.length_dropLast]; omega
  have hp : x <+: y.dropLast := by
    rcases List.prefix_or_prefix_of_prefix hxy (List.dropLast_prefix y) with h | h
    · exact h
    · have he := h.eq_of_length_le hlen
      rw [he]
  exact hx.1 (hp.trans hy.2)

/-- The physical off-spine child at a specified branching position is a first departure. -/
theorem offSpine_child (q r : Path) (i j : Fin 3) (hij : j ≠ i) :
    OffSpine (q ++ i :: r) (q ++ [j]) := by
  constructor
  · intro h
    have hc := (List.cons_prefix_cons.mp ((List.prefix_append_right_inj q).mp h)).1
    exact hij hc
  · rw [List.dropLast_concat]
    exact List.prefix_append _ _

/-- Framing two distinct first departures gives incomparable global roots. -/
theorem offSpine_roots_incomp {w : ℕ} (a : Fin w × Path) {p x y : Path}
    (hx : OffSpine p x) (hy : OffSpine p y) (hne : addrExt a x ≠ addrExt a y) :
    IncompAddr (addrExt a x) (addrExt a y) := by
  have hxy : x ≠ y := fun he => hne (congrArg (addrExt a) he)
  exact ⟨fun h => hx.not_prefix hy hxy ((below_same_root a x y).mp h),
    fun h => hy.not_prefix hx hxy.symm ((below_same_root a y x).mp h)⟩

/-- The carrier determines a side couple's partner among actual off-spine roots. -/
theorem SubCoupleAt.partner_unique_offSpine {G : Garden 2} (a f : Fin 2 × Path) {p x y : Path}
    (hx : OffSpine p x) (hy : OffSpine p y)
    (hfx : SubCoupleAt G f (addrExt a x)) (hfy : SubCoupleAt G f (addrExt a y)) :
    addrExt a x = addrExt a y := by
  by_contra hne
  have hi := offSpine_roots_incomp a hx hy hne
  obtain ⟨A,B,hA,hB,hAB⟩ := hfx
  obtain ⟨A',C,hA',hC,hAC⟩ := hfy
  have hAA : A' = A := Subtype.ext (hA'.trans hA.symm)
  subst A'
  have hBC : B.Incomparable C := by
    constructor
    · intro hb
      apply hi.1
      rw [← hB,← hC]
      exact ⟨hb.1.symm,hb.2⟩
    · intro hb
      apply hi.2
      rw [← hB,← hC]
      exact ⟨hb.1.symm,hb.2⟩
  exact no_incomparable_partner_roots hAB hAC hBC

/-- A lower side child is off the entire chain's terminal path. -/
theorem chain_back_offSpine (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (j : Fin 3) (hj : j ≠ k.lone) :
    OffSpine (RegChain.pair k r g i s).lonePath ([k.c] ++ i.lonePath ++ [j]) := by
  simpa only [RegChain.lonePath,List.append_assoc,List.singleton_append] using
    offSpine_child ([k.c] ++ i.lonePath) s.lonePath k.lone j hj

end WaveTurbulence.Reg

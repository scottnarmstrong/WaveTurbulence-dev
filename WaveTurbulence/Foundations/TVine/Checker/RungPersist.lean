/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.RungE

/-!
# Persistence of 2-cut rungs under gadget replacement

`rungL_gadget`: a 2-cut rung `{a, b}` of `es` stays a 2-cut rung after a gadget replacement of any bond that is
not a copy of `a = b`; its poles only grow (the gadget joins the pole of the replaced bond; a replaced rail is
re-routed through the gadget).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

/-! ## Symmetries -/

theorem rtg_symm_gen {α : Type*} {r : α → α → Prop} (hs : ∀ {a b}, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs hbc) ih

theorem adjIn_symm {G : UMultigraph ℕ} {X : Finset ℕ} {a b : ℕ} (h : AdjIn G X a b) : AdjIn G X b a :=
  ⟨h.2.1, h.1, by rw [Sym2.eq_swap]; exact h.2.2⟩

theorem rtg_adjIn_symm {G : UMultigraph ℕ} {X : Finset ℕ} {a b : ℕ} (h : Relation.ReflTransGen (AdjIn G X) a b) :
    Relation.ReflTransGen (AdjIn G X) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (adjIn_symm hbc) ih

theorem IsRungAt.swapAB {G : UMultigraph ℕ} {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ}
    (h : IsRungAt G a b xm xp ym yp Km Kp) : IsRungAt G b a ym yp xm xp Km Kp where
  ne := h.ne.symm
  a_mem := h.b_mem
  b_mem := h.a_mem
  mult_ab := by rw [Sym2.eq_swap]; exact h.mult_ab
  disj := h.disj
  union := by rw [h.union, Finset.erase_right_comm]
  connm := h.connm
  connp := h.connp
  noBond := h.noBond
  xm_mem := h.ym_mem
  xp_mem := h.yp_mem
  ym_mem := h.xm_mem
  yp_mem := h.xp_mem
  a_xm := h.b_ym
  a_xp := h.b_yp
  b_ym := h.a_xm
  b_yp := h.a_xp
  a_other := h.b_other
  b_other := h.a_other

theorem IsRungAt.swapPoles {G : UMultigraph ℕ} {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ}
    (h : IsRungAt G a b xm xp ym yp Km Kp) : IsRungAt G a b xp xm yp ym Kp Km where
  ne := h.ne
  a_mem := h.a_mem
  b_mem := h.b_mem
  mult_ab := h.mult_ab
  disj := h.disj.symm
  union := by rw [Finset.union_comm, h.union]
  connm := h.connp
  connp := h.connm
  noBond := fun u hu w hw => by rw [Sym2.eq_swap]; exact h.noBond w hw u hu
  xm_mem := h.xp_mem
  xp_mem := h.xm_mem
  ym_mem := h.yp_mem
  yp_mem := h.ym_mem
  a_xm := h.a_xp
  a_xp := h.a_xm
  b_ym := h.b_yp
  b_yp := h.b_ym
  a_other := fun z h1 h2 h3 => h.a_other z h1 h3 h2
  b_other := fun z h1 h2 h3 => h.b_other z h1 h3 h2

theorem ofEdges_eq_of_sameMult {es es' : Edges} (h : SameMult es es') : ofEdges es = ofEdges es' := by
  apply Core.ext
  · ext z; rw [mem_ofEdges_verts, mem_ofEdges_verts]
    exact ⟨fun hz => h.inEnds hz, fun hz => h.symm.inEnds hz⟩
  · intro e
    induction e using Sym2.ind with
    | _ u v => rw [ofEdges_mult, ofEdges_mult, h u v]

theorem eraseOne_comm (es : Edges) (x y : ℕ) : eraseOne es x y = eraseOne es y x := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [eraseOne, isPair_comm x y e, ih]

theorem GadgetOK.flip {es : Edges} {x y w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ}
    (h : GadgetOK es x y w₁ w₂ inner W) : GadgetOK es y x w₂ w₁ inner W := by
  have hsymm : ∀ {u v}, (u ∈ W ∧ v ∈ W ∧ mult inner u v ≠ 0) → (v ∈ W ∧ u ∈ W ∧ mult inner v u ≠ 0) :=
    fun hh => ⟨hh.2.1, hh.1, by rw [mult_comm]; exact hh.2.2⟩
  refine ⟨by rw [mult_comm]; exact h.hxy, h.x_ne_y.symm, h.w₂_mem, h.w₁_mem, h.fresh, h.inner_in, ?_⟩
  intro w hw
  exact (rtg_symm_gen hsymm (h.conn w₂ h.w₂_mem)).trans (h.conn w hw)

theorem gadget_flip_sameMult (es : Edges) (x y w₁ w₂ : ℕ) (inner : Edges) :
    SameMult (gadget es x y w₁ w₂ inner) (gadget es y x w₂ w₁ inner) := by
  intro u v
  simp only [gadget, gadgetList, eraseOne_comm es x y, mult_append, mult_list_cons, mult_nil]
  rw [ind_swap u v x w₁, ind_swap u v w₂ y]; omega

/-! ## The two core cases -/

section core

variable {es : Edges} {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ}

theorem RungL.mem_ends (hR : RungL es a b xm xp ym yp Km Kp) {z : ℕ} (hz : z ∈ Km ∨ z ∈ Kp) :
    InEnds es z ∧ z ≠ a ∧ z ≠ b := by
  have : z ∈ Km ∪ Kp := Finset.mem_union.mpr hz
  rw [hR.union] at this
  simp only [Finset.mem_erase] at this
  exact ⟨mem_ofEdges_verts.mp this.2.2, this.2.1, this.1⟩

theorem RungL.a_ends (hR : RungL es a b xm xp ym yp Km Kp) : InEnds es a := mem_ofEdges_verts.mp hR.a_mem
theorem RungL.b_ends (hR : RungL es a b xm xp ym yp Km Kp) : InEnds es b := mem_ofEdges_verts.mp hR.b_mem

/-- Paths inside a set, moved to a new graph edge by edge. -/
theorem rtg_map {G H : UMultigraph ℕ} {X Y : Finset ℕ}
    (hstep : ∀ p q, AdjIn G X p q → Relation.ReflTransGen (AdjIn H Y) p q) {u v : ℕ}
    (h : Relation.ReflTransGen (AdjIn G X) u v) : Relation.ReflTransGen (AdjIn H Y) u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)

/-- The gadget's atoms, reached from `w₁` inside `W ⊆ Y`. -/
theorem gadget_conn {x y w₁ w₂ : ℕ} {inner : Edges} {W Y : Finset ℕ} (hG : GadgetOK es x y w₁ w₂ inner W)
    (hWY : W ⊆ Y) {w : ℕ} (hw : w ∈ W) :
    Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) Y) w₁ w := by
  have hc := hG.conn w hw
  clear hw
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | @tail p q _ hpq ih =>
    refine ih.tail ⟨hWY hpq.1, hWY hpq.2.1, ?_⟩
    rw [ofEdges_mult, hG.mult_in_new hpq.1 hpq.2.1]; exact hpq.2.2

/-- **Pole case**: the replaced bond lies in the pole `Km`. -/
theorem rungL_gadget_pole (hR : RungL es a b xm xp ym yp Km Kp) {x y w₁ w₂ : ℕ} {inner : Edges}
    {W : Finset ℕ} (hG : GadgetOK es x y w₁ w₂ inner W) (hx : x ∈ Km) (hy : y ∈ Km) :
    RungL (gadget es x y w₁ w₂ inner) a b xm xp ym yp (Km ∪ W) Kp := by
  have hxe := hR.mem_ends (Or.inl hx)
  have hye := hR.mem_ends (Or.inl hy)
  have haW : a ∉ W := fun h => hG.fresh a h hR.a_ends
  have hbW : b ∉ W := fun h => hG.fresh b h hR.b_ends
  have hKpW : ∀ z ∈ Kp, z ∉ W := fun z hz h => hG.fresh z h (hR.mem_ends (Or.inr hz)).1
  have hKmW : ∀ z ∈ Km, z ∉ W := fun z hz h => hG.fresh z h (hR.mem_ends (Or.inl hz)).1
  have xKp : x ∉ Kp := Finset.disjoint_left.mp hR.disj hx
  have yKp : y ∉ Kp := Finset.disjoint_left.mp hR.disj hy
  -- multiplicities of old pairs avoiding `x` or `y`
  have keep : ∀ u v, u ∉ W → v ∉ W → (u ≠ x ∧ u ≠ y) → mult (gadget es x y w₁ w₂ inner) u v = mult es u v := by
    intro u v hu hv huxy
    have := hG.mult_old hu hv
    rw [ind_eq_zero (u := u) (v := v) (x := x) (y := y) (by omega)] at this; omega
  have rkeep : ∀ u v, u ∉ W → v ∉ W → mult (gadget es x y w₁ w₂ inner) u v ≤ mult es u v := by
    intro u v hu hv; have := hG.mult_old hu hv; omega
  have mem' : ∀ z, z ∈ (ofEdges (gadget es x y w₁ w₂ inner)).verts ↔ InEnds es z ∨ z ∈ W := by
    intro z; rw [mem_ofEdges_verts, hG.inEnds_gadget]
  refine ⟨hR.ne, (mem' a).mpr (Or.inl hR.a_ends), (mem' b).mpr (Or.inl hR.b_ends), ?_, ?_, ?_, ?_, ?_, ?_,
    Finset.mem_union_left _ hR.xm_mem, hR.xp_mem, Finset.mem_union_left _ hR.ym_mem, hR.yp_mem, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [ofEdges_mult, keep a b haW hbW ⟨hxe.2.1.symm, hye.2.1.symm⟩, ← ofEdges_mult]; exact hR.mult_ab
  · exact Finset.disjoint_union_left.mpr ⟨hR.disj, Finset.disjoint_left.mpr fun z hz hz' => hKpW z hz' hz⟩
  · ext z
    have hu := congrArg (z ∈ ·) hR.union
    simp only [Finset.mem_union, Finset.mem_erase, mem' z, mem_ofEdges_verts] at hu ⊢
    constructor
    · rintro ((h | h) | h)
      · exact ⟨(hR.mem_ends (Or.inl h)).2.2, (hR.mem_ends (Or.inl h)).2.1, Or.inl (hR.mem_ends (Or.inl h)).1⟩
      · exact ⟨fun hh => hbW (hh ▸ h), fun hh => haW (hh ▸ h), Or.inr h⟩
      · exact ⟨(hR.mem_ends (Or.inr h)).2.2, (hR.mem_ends (Or.inr h)).2.1, Or.inl (hR.mem_ends (Or.inr h)).1⟩
    · rintro ⟨h1, h2, h3 | h3⟩
      · rcases hu.mpr ⟨h1, h2, h3⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · exact Or.inl (Or.inr h3)
  · -- the pole `Km ∪ W` is connected (through `x`)
    have stepKm : ∀ p q, AdjIn (ofEdges es) Km p q →
        Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W)) p q := by
      intro p q ⟨hp, hq, hpq⟩
      rw [ofEdges_mult] at hpq
      have hpW := hKmW p hp; have hqW := hKmW q hq
      have hold := hG.mult_old hpW hqW
      by_cases hn : mult (gadget es x y w₁ w₂ inner) p q = 0
      · -- the replaced copy: go through the gadget
        have hi : ind p q x y = 1 := by unfold ind at hold ⊢; split_ifs at hold ⊢ <;> omega
        have hpq' : s(p, q) = s(x, y) := by
          by_contra hh; unfold ind at hi; rw [if_neg hh] at hi; omega
        have hxw : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W) x w₁ :=
          ⟨Finset.mem_union_left _ hx, Finset.mem_union_right _ hG.w₁_mem, by
            rw [ofEdges_mult, hG.mult_x_new hG.w₁_mem, if_pos rfl]; omega⟩
        have hwy : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W) w₂ y :=
          ⟨Finset.mem_union_right _ hG.w₂_mem, Finset.mem_union_left _ hy, by
            rw [ofEdges_mult, mult_comm, hG.mult_y_new hG.w₂_mem, if_pos rfl]; omega⟩
        have path : Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W)) x y :=
          (Relation.ReflTransGen.single hxw).trans
            ((gadget_conn hG Finset.subset_union_right hG.w₂_mem).tail hwy)
        rw [Sym2.eq_iff] at hpq'
        rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact path
        · exact rtg_adjIn_symm path
      · exact Relation.ReflTransGen.single ⟨Finset.mem_union_left _ hp, Finset.mem_union_left _ hq, by
          rw [ofEdges_mult]; exact hn⟩
    have toX : ∀ u ∈ Km ∪ W,
        Relation.ReflTransGen (AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W)) x u := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact rtg_map stepKm (hR.connm x hx u hu)
      · have hxw : AdjIn (ofEdges (gadget es x y w₁ w₂ inner)) (Km ∪ W) x w₁ :=
          ⟨Finset.mem_union_left _ hx, Finset.mem_union_right _ hG.w₁_mem, by
            rw [ofEdges_mult, hG.mult_x_new hG.w₁_mem, if_pos rfl]; omega⟩
        exact (Relation.ReflTransGen.single hxw).trans (gadget_conn hG Finset.subset_union_right hu)
    intro u hu v hv
    exact (rtg_adjIn_symm (toX u hu)).trans (toX v hv)
  · refine fun u hu v hv => rtg_map (fun p q ⟨hp, hq, hpq⟩ => Relation.ReflTransGen.single ⟨hp, hq, ?_⟩)
      (hR.connp u hu v hv)
    rw [ofEdges_mult, keep p q (hKpW p hp) (hKpW q hq) ⟨fun h => xKp (h ▸ hp), fun h => yKp (h ▸ hp)⟩,
      ← ofEdges_mult]; exact hpq
  · intro u hu w hw
    rw [ofEdges_mult]
    rcases Finset.mem_union.mp hu with hu | hu
    · have := rkeep u w (hKmW u hu) (hKpW w hw)
      have h0 := hR.noBond u hu w hw; rw [ofEdges_mult] at h0; omega
    · rw [mult_comm]
      exact hG.mult_new_zero (hKpW w hw) (fun h => xKp (h ▸ hw)) (fun h => yKp (h ▸ hw)) hu
  all_goals first
    | (rw [ofEdges_mult, keep _ _ haW (by first | exact hKmW _ hR.xm_mem | exact hKpW _ hR.xp_mem)
          ⟨hxe.2.1.symm, hye.2.1.symm⟩, ← ofEdges_mult]
       first | exact hR.a_xm | exact hR.a_xp)
    | (rw [ofEdges_mult, keep _ _ hbW (by first | exact hKmW _ hR.ym_mem | exact hKpW _ hR.yp_mem)
          ⟨hxe.2.2.symm, hye.2.2.symm⟩, ← ofEdges_mult]
       first | exact hR.b_ym | exact hR.b_yp)
    | skip
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    by_cases hz : z ∈ W
    · exact hG.mult_new_zero haW hxe.2.1.symm hye.2.1.symm hz
    · have := rkeep a z haW hz; have h0 := hR.a_other z h1 h2 h3; rw [ofEdges_mult] at h0; omega
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    by_cases hz : z ∈ W
    · exact hG.mult_new_zero hbW hxe.2.2.symm hye.2.2.symm hz
    · have := rkeep b z hbW hz; have h0 := hR.b_other z h1 h2 h3; rw [ofEdges_mult] at h0; omega

end core

section core2

variable {es : Edges} {a b xm xp ym yp : ℕ} {Km Kp : Finset ℕ}

/-- **Rail case**: the replaced bond is the rail `a–xm`; the new rail is `a–w₁`. -/
theorem rungL_gadget_rail (hR : RungL es a b xm xp ym yp Km Kp) {w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ}
    (hG : GadgetOK es a xm w₁ w₂ inner W) :
    RungL (gadget es a xm w₁ w₂ inner) a b w₁ xp ym yp (Km ∪ W) Kp := by
  have hxm := hR.mem_ends (Or.inl hR.xm_mem)
  have haW : a ∉ W := fun h => hG.fresh a h hR.a_ends
  have hbW : b ∉ W := fun h => hG.fresh b h hR.b_ends
  have hKpW : ∀ z ∈ Kp, z ∉ W := fun z hz h => hG.fresh z h (hR.mem_ends (Or.inr hz)).1
  have hKmW : ∀ z ∈ Km, z ∉ W := fun z hz h => hG.fresh z h (hR.mem_ends (Or.inl hz)).1
  have xmKp : xm ∉ Kp := Finset.disjoint_left.mp hR.disj hR.xm_mem
  have keep : ∀ u v, u ∉ W → v ∉ W → ¬ ((u = a ∧ v = xm) ∨ (u = xm ∧ v = a)) →
      mult (gadget es a xm w₁ w₂ inner) u v = mult es u v := by
    intro u v hu hv huv
    have := hG.mult_old hu hv
    rw [ind_eq_zero huv] at this; omega
  have mem' : ∀ z, z ∈ (ofEdges (gadget es a xm w₁ w₂ inner)).verts ↔ InEnds es z ∨ z ∈ W := by
    intro z; rw [mem_ofEdges_verts, hG.inEnds_gadget]
  have Kp_ne : ∀ z ∈ Kp, z ≠ a ∧ z ≠ xm := fun z hz =>
    ⟨(hR.mem_ends (Or.inr hz)).2.1, fun h => xmKp (h ▸ hz)⟩
  have hxw : AdjIn (ofEdges (gadget es a xm w₁ w₂ inner)) (Km ∪ W) w₂ xm :=
    ⟨Finset.mem_union_right _ hG.w₂_mem, Finset.mem_union_left _ hR.xm_mem, by
      rw [ofEdges_mult, mult_comm, hG.mult_y_new hG.w₂_mem, if_pos rfl]; omega⟩
  refine ⟨hR.ne, (mem' a).mpr (Or.inl hR.a_ends), (mem' b).mpr (Or.inl hR.b_ends), ?_, ?_, ?_, ?_, ?_, ?_,
    Finset.mem_union_right _ hG.w₁_mem, hR.xp_mem, Finset.mem_union_left _ hR.ym_mem, hR.yp_mem, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [ofEdges_mult, keep a b haW hbW (by have := hxm.2.2; have := hR.ne; omega), ← ofEdges_mult]
    exact hR.mult_ab
  · exact Finset.disjoint_union_left.mpr ⟨hR.disj, Finset.disjoint_left.mpr fun z hz hz' => hKpW z hz' hz⟩
  · ext z
    have hu := congrArg (z ∈ ·) hR.union
    simp only [Finset.mem_union, Finset.mem_erase, mem' z, mem_ofEdges_verts] at hu ⊢
    constructor
    · rintro ((h | h) | h)
      · exact ⟨(hR.mem_ends (Or.inl h)).2.2, (hR.mem_ends (Or.inl h)).2.1, Or.inl (hR.mem_ends (Or.inl h)).1⟩
      · exact ⟨fun hh => hbW (hh ▸ h), fun hh => haW (hh ▸ h), Or.inr h⟩
      · exact ⟨(hR.mem_ends (Or.inr h)).2.2, (hR.mem_ends (Or.inr h)).2.1, Or.inl (hR.mem_ends (Or.inr h)).1⟩
    · rintro ⟨h1, h2, h3 | h3⟩
      · rcases hu.mpr ⟨h1, h2, h3⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · exact Or.inl (Or.inr h3)
  · have stepKm : ∀ p q, AdjIn (ofEdges es) Km p q →
        Relation.ReflTransGen (AdjIn (ofEdges (gadget es a xm w₁ w₂ inner)) (Km ∪ W)) p q := by
      intro p q ⟨hp, hq, hpq⟩
      refine Relation.ReflTransGen.single ⟨Finset.mem_union_left _ hp, Finset.mem_union_left _ hq, ?_⟩
      have := (hR.mem_ends (Or.inl hp)).2.1; have := (hR.mem_ends (Or.inl hq)).2.1
      rw [ofEdges_mult, keep p q (hKmW p hp) (hKmW q hq) (by omega), ← ofEdges_mult]; exact hpq
    have toXm : ∀ u ∈ Km ∪ W,
        Relation.ReflTransGen (AdjIn (ofEdges (gadget es a xm w₁ w₂ inner)) (Km ∪ W)) xm u := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact rtg_map stepKm (hR.connm xm hR.xm_mem u hu)
      · exact (Relation.ReflTransGen.single (adjIn_symm hxw)).trans
          ((rtg_adjIn_symm (gadget_conn hG Finset.subset_union_right hG.w₂_mem)).trans
            (gadget_conn hG Finset.subset_union_right hu))
    intro u hu v hv
    exact (rtg_adjIn_symm (toXm u hu)).trans (toXm v hv)
  · refine fun u hu v hv => rtg_map (fun p q ⟨hp, hq, hpq⟩ => Relation.ReflTransGen.single ⟨hp, hq, ?_⟩)
      (hR.connp u hu v hv)
    have := Kp_ne p hp; have := Kp_ne q hq
    rw [ofEdges_mult, keep p q (hKpW p hp) (hKpW q hq) (by omega), ← ofEdges_mult]; exact hpq
  · intro u hu w hw
    rw [ofEdges_mult]
    have := Kp_ne w hw
    rcases Finset.mem_union.mp hu with hu | hu
    · rw [keep u w (hKmW u hu) (hKpW w hw) (by omega)]
      have h0 := hR.noBond u hu w hw; rwa [ofEdges_mult] at h0
    · rw [mult_comm]; exact hG.mult_new_zero (hKpW w hw) this.1 this.2 hu
  · rw [ofEdges_mult, hG.mult_x_new hG.w₁_mem, if_pos rfl]
  · have := Kp_ne xp hR.xp_mem
    rw [ofEdges_mult, keep a xp haW (hKpW _ hR.xp_mem) (by omega), ← ofEdges_mult]; exact hR.a_xp
  · have := (hR.mem_ends (Or.inl hR.ym_mem)).2; have := hR.ne
    rw [ofEdges_mult, keep b ym hbW (hKmW _ hR.ym_mem) (by have := hxm.2.2; omega), ← ofEdges_mult]
    exact hR.b_ym
  · have := (hR.mem_ends (Or.inr hR.yp_mem)).2; have := hR.ne
    rw [ofEdges_mult, keep b yp hbW (hKpW _ hR.yp_mem) (by have := hxm.2.2; omega), ← ofEdges_mult]
    exact hR.b_yp
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    by_cases hz : z ∈ W
    · rw [hG.mult_x_new hz, if_neg h2]
    by_cases hzx : z = xm
    · subst hzx
      have := hG.mult_old haW hz
      rw [ind_eq_one (Or.inl ⟨rfl, rfl⟩)] at this
      have h0 := hR.a_xm; rw [ofEdges_mult] at h0; omega
    · rw [keep a z haW hz (by omega)]
      have h0 := hR.a_other z h1 hzx h3; rwa [ofEdges_mult] at h0
  · intro z h1 h2 h3
    rw [ofEdges_mult]
    have hba := hR.ne
    by_cases hz : z ∈ W
    · exact hG.mult_new_zero hbW (Ne.symm hba) hxm.2.2.symm hz
    · rw [keep b z hbW hz (by have := hxm.2.2; omega)]
      have h0 := hR.b_other z h1 h2 h3; rwa [ofEdges_mult] at h0

/-- The replaced bond is at `a` (a rail). -/
theorem rungL_gadget_at_a (hR : RungL es a b xm xp ym yp Km Kp) {y w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ}
    (hG : GadgetOK es a y w₁ w₂ inner W) (hyb : y ≠ b) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (gadget es a y w₁ w₂ inner) a b xm' xp' ym' yp' Km' Kp' ∧
      Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  have hy : y = xm ∨ y = xp := by
    by_contra hh
    rw [not_or] at hh
    have := hR.a_other y hyb hh.1 hh.2
    rw [ofEdges_mult] at this; exact hG.hxy this
  rcases hy with rfl | rfl
  · exact ⟨_, _, _, _, _, _, rungL_gadget_rail hR hG, Finset.subset_union_left, subset_refl _⟩
  · exact ⟨_, _, _, _, _, _, IsRungAt.swapPoles (rungL_gadget_rail (IsRungAt.swapPoles hR) hG), subset_refl _,
      Finset.subset_union_left⟩

/-- The replaced bond is at an end of the rung. -/
theorem rungL_gadget_at_ab (hR : RungL es a b xm xp ym yp Km Kp) {x y w₁ w₂ : ℕ} {inner : Edges}
    {W : Finset ℕ} (hG : GadgetOK es x y w₁ w₂ inner W) (hne : s(x, y) ≠ s(a, b)) (hx : x = a ∨ x = b) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (gadget es x y w₁ w₂ inner) a b xm' xp' ym' yp' Km' Kp' ∧
      Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  rcases hx with rfl | rfl
  · exact rungL_gadget_at_a hR hG (fun h => hne (by rw [h]))
  · obtain ⟨_, _, _, _, Km', Kp', h, h1, h2⟩ :=
      rungL_gadget_at_a (IsRungAt.swapAB hR) hG (fun h => hne (by rw [h, Sym2.eq_swap]))
    exact ⟨_, _, _, _, Km', Kp', IsRungAt.swapAB h, h1, h2⟩

/-- **Persistence**: a gadget replacement of a bond other than a copy of `a = b` keeps `{a, b}` a 2-cut rung, and
its poles only grow. -/
theorem rungL_gadget (hR : RungL es a b xm xp ym yp Km Kp) {x y w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ}
    (hG : GadgetOK es x y w₁ w₂ inner W) (hne : s(x, y) ≠ s(a, b)) :
    ∃ xm' xp' ym' yp' Km' Kp', RungL (gadget es x y w₁ w₂ inner) a b xm' xp' ym' yp' Km' Kp' ∧
      Km ⊆ Km' ∧ Kp ⊆ Kp' := by
  by_cases hx : x = a ∨ x = b
  · exact rungL_gadget_at_ab hR hG hne hx
  by_cases hy : y = a ∨ y = b
  · obtain ⟨xm', xp', ym', yp', Km', Kp', h, h1, h2⟩ :=
      rungL_gadget_at_ab hR hG.flip (fun h => hne (by rw [Sym2.eq_swap]; exact h)) hy
    have e := ofEdges_eq_of_sameMult (gadget_flip_sameMult es x y w₁ w₂ inner)
    refine ⟨xm', xp', ym', yp', Km', Kp', ?_, h1, h2⟩
    show IsRungAt (ofEdges _) _ _ _ _ _ _ _ _
    rw [e]; exact h
  rw [not_or] at hx hy
  have hxK : x ∈ Km ∪ Kp := by
    rw [hR.union]; simp only [Finset.mem_erase]; exact ⟨hx.2, hx.1, mem_ofEdges_verts.mpr hG.x_ends⟩
  have hyK : y ∈ Km ∪ Kp := by
    rw [hR.union]; simp only [Finset.mem_erase]; exact ⟨hy.2, hy.1, mem_ofEdges_verts.mpr hG.y_ends⟩
  rcases Finset.mem_union.mp hxK with hxK | hxK <;> rcases Finset.mem_union.mp hyK with hyK | hyK
  · exact ⟨_, _, _, _, _, _, rungL_gadget_pole hR hG hxK hyK, Finset.subset_union_left, subset_refl _⟩
  · exfalso; have := hR.noBond x hxK y hyK; rw [ofEdges_mult] at this; exact hG.hxy this
  · exfalso; have := hR.noBond y hyK x hxK; rw [ofEdges_mult, mult_comm] at this; exact hG.hxy this
  · exact ⟨_, _, _, _, _, _, IsRungAt.swapPoles (rungL_gadget_pole (IsRungAt.swapPoles hR) hG hxK hyK), subset_refl _,
      Finset.subset_union_left⟩

end core2

end WaveTurbulence.TVine.Checker

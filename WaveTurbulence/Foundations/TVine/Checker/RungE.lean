/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.GenBlock

/-!
# 2-cut rungs of bond lists under gadget replacement (towards N2 Lemma 1.8)

A *gadget replacement* replaces one copy of the bond `x–y` by `x–w₁`, a connected multigraph `inner` on fresh atoms
`W`, and `w₂–y`. The (Z1) move (`W = {a, b}`, `inner` the triple bond) and the subdivision by one joint or by two
adjacent joints are gadget replacements.

* `RungL es …`: L1's `IsRungAt` for the multigraph `ofEdges es` (N2 Def 1.3);
* `rungL_gadget_pole`, `rungL_gadget_rail`: a 2-cut rung persists under a gadget replacement of a bond other than
  a copy of its double bond (the gadget joins the pole of the bond; a replaced rail is re-routed).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

/-- L1's 2-cut rung (`IsRungAt`), read in the multigraph of a bond list. -/
abbrev RungL (es : Edges) (a b xm xp ym yp : ℕ) (Km Kp : Finset ℕ) : Prop :=
  IsRungAt (ofEdges es) a b xm xp ym yp Km Kp

/-- The gadget bonds: `x–w₁`, the inner bonds, `w₂–y`. -/
def gadgetList (x y w₁ w₂ : ℕ) (inner : Edges) : Edges := (x, w₁) :: (inner ++ [(w₂, y)])

/-- Replace one copy of `x–y` by the gadget. -/
def gadget (es : Edges) (x y w₁ w₂ : ℕ) (inner : Edges) : Edges := eraseOne es x y ++ gadgetList x y w₁ w₂ inner

theorem z1_eq_gadget (es : Edges) (x y a b : ℕ) : z1 es x y a b = gadget es x y a b [(a, b), (a, b), (a, b)] := rfl

theorem placeOne_eq_gadget (es : Edges) (X Y J₁ J₂ : ℕ) :
    placeOne es X Y J₁ J₂ = gadget es X Y J₁ J₂ [(J₁, J₂)] := rfl

/-- The hypotheses on a gadget: fresh atoms `W ∋ w₁, w₂`, inner bonds inside `W`, `W` connected from `w₁`. -/
structure GadgetOK (es : Edges) (x y w₁ w₂ : ℕ) (inner : Edges) (W : Finset ℕ) : Prop where
  hxy : mult es x y ≠ 0
  x_ne_y : x ≠ y
  w₁_mem : w₁ ∈ W
  w₂_mem : w₂ ∈ W
  fresh : ∀ w ∈ W, ¬ InEnds es w
  inner_in : ∀ e ∈ inner, e.1 ∈ W ∧ e.2 ∈ W
  conn : ∀ w ∈ W, Relation.ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ mult inner u v ≠ 0) w₁ w

namespace GadgetOK

variable {es : Edges} {x y w₁ w₂ : ℕ} {inner : Edges} {W : Finset ℕ} (h : GadgetOK es x y w₁ w₂ inner W)
include h

theorem x_ends : InEnds es x := (inEnds_of_mult_ne_zero h.hxy).1
theorem y_ends : InEnds es y := (inEnds_of_mult_ne_zero h.hxy).2
theorem x_not_mem : x ∉ W := fun hx => h.fresh x hx h.x_ends
theorem y_not_mem : y ∉ W := fun hy => h.fresh y hy h.y_ends

theorem mult_inner_zero {u v : ℕ} (hu : u ∉ W ∨ v ∉ W) : mult inner u v = 0 := by
  unfold mult
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he hp
  have := h.inner_in e he
  rcases (isPair_iff u v e).mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hu with hu | hu <;> simp_all

/-- The multiplicities after the replacement. -/
theorem mult_gadget (u v : ℕ) :
    mult (gadget es x y w₁ w₂ inner) u v + ind u v x y =
      mult es u v + ind u v x w₁ + mult inner u v + ind u v w₂ y := by
  have := mult_eraseOne' h.hxy u v
  simp only [gadget, gadgetList, mult_append, mult_list_cons, mult_nil]
  omega

theorem ne_of_mem_W {z w : ℕ} (hz : z ∉ W) (hw : w ∈ W) : z ≠ w := fun hh => hz (hh ▸ hw)

/-- Old pairs. -/
theorem mult_old {u v : ℕ} (hu : u ∉ W) (hv : v ∉ W) :
    mult (gadget es x y w₁ w₂ inner) u v + ind u v x y = mult es u v := by
  have := h.mult_gadget u v
  have a1 := h.ne_of_mem_W hu h.w₁_mem; have a2 := h.ne_of_mem_W hv h.w₁_mem
  have b1 := h.ne_of_mem_W hu h.w₂_mem; have b2 := h.ne_of_mem_W hv h.w₂_mem
  rw [ind_eq_zero (u := u) (v := v) (x := x) (y := w₁) (by omega),
    ind_eq_zero (u := u) (v := v) (x := w₂) (y := y) (by omega), h.mult_inner_zero (Or.inl hu)] at this
  omega

/-- An old atom other than `x, y` has no bond into `W`. -/
theorem mult_new_zero {u w : ℕ} (hu : u ∉ W) (hux : u ≠ x) (huy : u ≠ y) (hw : w ∈ W) :
    mult (gadget es x y w₁ w₂ inner) u w = 0 := by
  have := h.mult_gadget u w
  have a1 := h.ne_of_mem_W hu h.w₁_mem; have b1 := h.ne_of_mem_W hu h.w₂_mem
  rw [mult_eq_zero_of_not_inEnds' (h.fresh w hw), ind_eq_zero (u := u) (v := w) (x := x) (y := y) (by omega),
    ind_eq_zero (u := u) (v := w) (x := x) (y := w₁) (by omega), h.mult_inner_zero (Or.inl hu),
    ind_eq_zero (u := u) (v := w) (x := w₂) (y := y) (by omega)] at this
  omega

/-- The bonds from `x` into `W`. -/
theorem mult_x_new {w : ℕ} (hw : w ∈ W) : mult (gadget es x y w₁ w₂ inner) x w = if w = w₁ then 1 else 0 := by
  have := h.mult_gadget x w
  have hxW := h.x_not_mem
  have hyw := h.ne_of_mem_W h.y_not_mem hw
  have hxw₂ := h.ne_of_mem_W hxW h.w₂_mem
  have hxy := h.x_ne_y
  rw [mult_eq_zero_of_not_inEnds' (h.fresh w hw), ind_eq_zero (u := x) (v := w) (x := x) (y := y) (by omega),
    ind_right _ _ _ (h.ne_of_mem_W hxW h.w₁_mem), h.mult_inner_zero (Or.inl hxW),
    ind_eq_zero (u := x) (v := w) (x := w₂) (y := y) (by omega)] at this
  omega

/-- The bonds from `y` into `W`. -/
theorem mult_y_new {w : ℕ} (hw : w ∈ W) : mult (gadget es x y w₁ w₂ inner) y w = if w = w₂ then 1 else 0 := by
  have := h.mult_gadget y w
  have hyW := h.y_not_mem
  have hxw := h.ne_of_mem_W h.x_not_mem hw
  have hyw₁ := h.ne_of_mem_W hyW h.w₁_mem
  have hxy := h.x_ne_y
  rw [mult_eq_zero_of_not_inEnds' (h.fresh w hw), ind_eq_zero (u := y) (v := w) (x := x) (y := y) (by omega),
    ind_eq_zero (u := y) (v := w) (x := x) (y := w₁) (by omega), h.mult_inner_zero (Or.inl hyW),
    ind_left _ _ _ (h.ne_of_mem_W hyW h.w₂_mem)] at this
  omega

/-- Bonds inside `W`. -/
theorem mult_in_new {w w' : ℕ} (hw : w ∈ W) (hw' : w' ∈ W) :
    mult (gadget es x y w₁ w₂ inner) w w' = mult inner w w' := by
  have := h.mult_gadget w w'
  have a := h.ne_of_mem_W h.x_not_mem hw; have a' := h.ne_of_mem_W h.x_not_mem hw'
  have b := h.ne_of_mem_W h.y_not_mem hw; have b' := h.ne_of_mem_W h.y_not_mem hw'
  rw [mult_eq_zero_of_not_inEnds (h.fresh w hw), ind_eq_zero (u := w) (v := w') (x := x) (y := y) (by omega),
    ind_eq_zero (u := w) (v := w') (x := x) (y := w₁) (by omega),
    ind_eq_zero (u := w) (v := w') (x := w₂) (y := y) (by omega)] at this
  omega

/-- The ends after the replacement. -/
theorem inEnds_gadget (z : ℕ) : InEnds (gadget es x y w₁ w₂ inner) z ↔ InEnds es z ∨ z ∈ W := by
  constructor
  · intro hz
    rcases inEnds_append.mp hz with hz | ⟨e, he, hz⟩
    · exact Or.inl (inEnds_eraseOne hz)
    · simp only [gadgetList, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at he
      rcases he with rfl | he | rfl
      · rcases hz with hz | hz
        · exact Or.inl (hz ▸ h.x_ends)
        · exact Or.inr (hz ▸ h.w₁_mem)
      · have := h.inner_in e he
        rcases hz with hz | hz
        · exact Or.inr (hz ▸ this.1)
        · exact Or.inr (hz ▸ this.2)
      · rcases hz with hz | hz
        · exact Or.inr (hz ▸ h.w₂_mem)
        · exact Or.inl (hz ▸ h.y_ends)
  · rintro (hz | hz)
    · by_cases hzx : z = x
      · exact inEnds_append.mpr (Or.inr ⟨(x, w₁), by simp [gadgetList], Or.inl hzx.symm⟩)
      by_cases hzy : z = y
      · exact inEnds_append.mpr (Or.inr ⟨(w₂, y), by simp [gadgetList], Or.inr hzy.symm⟩)
      obtain ⟨w, hw⟩ := inEnds_iff.mp hz
      have hzW : z ∉ W := fun hh => h.fresh z hh hz
      by_cases hwW : w ∈ W
      · exact absurd (mult_eq_zero_of_not_inEnds' (es := es) (u := z) (h.fresh w hwW)) hw
      · refine inEnds_iff.mpr ⟨w, ?_⟩
        have := h.mult_old hzW hwW
        rw [ind_eq_zero (by omega)] at this; omega
    · obtain ⟨n, hn⟩ : ∃ n, Relation.ReflTransGen (fun u v => u ∈ W ∧ v ∈ W ∧ mult inner u v ≠ 0) w₁ z ∧ n = 0 :=
        ⟨0, h.conn z hz, rfl⟩
      rcases Relation.ReflTransGen.cases_tail hn.1 with heq | ⟨c, _, hc⟩
      · exact inEnds_append.mpr (Or.inr ⟨(x, w₁), by simp [gadgetList], Or.inr heq.symm⟩)
      · obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hc.2.2)
        rw [List.mem_filter] at he
        rcases (isPair_iff c z e).mp he.2 with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact inEnds_append.mpr (Or.inr ⟨e, by simp [gadgetList, he.1], Or.inr h2⟩)
        · exact inEnds_append.mpr (Or.inr ⟨e, by simp [gadgetList, he.1], Or.inl h1⟩)

end GadgetOK

end WaveTurbulence.TVine.Checker

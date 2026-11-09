/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.RungCore

/-!
# Rung deletion and a move inside a pole (M4 §5.3, cases (i)–(iii))

Let `R = {a, b}` carry `RungCore` with poles `Km, Kp`, and let `P = {p, q} ⊆ Km` be a (Y2) pair with externals
`p', q'`. The cases of M4 §5.3 (REF-M4 §2.3, R3):
* (i) `rung_case_i`: `p', q' ∈ Km`; the move commutes with the deletion, and `R` keeps its rails;
* (ii) `rung_case_ii`: `p' = a` (so `p = xm`), `q' ∈ Km`; `a`'s rail moves to `q'`, and in `G/[μ]R` the external
  of `p` is its cross partner;
* (iii) `rung_case_iii`: `p' = a`, `q' = b` (so `P = {xm, ym}`, the pole collapses); `R` becomes a (Y2) pair
  (or is stuck if `xp = yp`), and `(G/[μ]R)/P = (G/P)/R`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

theorem count_pair (e x y : Sym2 V) :
    ({x, y} : Multiset (Sym2 V)).count e = (if e = x then 1 else 0) + (if e = y then 1 else 0) := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, add_comm]

/-- Two (Y2) pairs on graphs with the same bonds at `p` and `q`. -/
theorem IsY2Pair.congr {G G' : UMultigraph V} {p q p' q' : V} (h : IsY2Pair G p q p' q')
    (hp : ∀ x, G'.mult s(p, x) = G.mult s(p, x)) (hq : ∀ x, G'.mult s(q, x) = G.mult s(q, x)) :
    IsY2Pair G' p q p' q' :=
  IsY2Pair.of_mult h.ne h.ext_ne h.c_ne_a h.c_ne_b h.d_ne_a h.d_ne_b (fun x => (hp x).trans (h.mult_a x))
    (fun x => (hq x).trans (h.mult_b x))

/-- Assembly of a path step: a move `P` of `G` commuting with the surgery. -/
theorem cons_assemble {G D T' : UMultigraph V} {p q p₁ q₁ : V} {z : Sym2 V} {rest : List (Sym2 V)}
    (hne : s(p, q) ≠ z) (hP : IsY2Pair G p q p₁ q₁) (hcomm : y2Move G p q p₁ q₁ = D)
    (ih : rest.count z = 1 ∧ Y2Path D (rest.erase z) T') :
    (s(p, q) :: rest).count z = 1 ∧ Y2Path G ((s(p, q) :: rest).erase z) T' := by
  refine ⟨?_, ?_⟩
  · rw [List.count_cons, ih.1]; simp [hne]
  · rw [List.erase_cons_tail (by simpa using hne)]
    exact .cons hP (hcomm ▸ ih.2)

section Cases

variable {C : UMultigraph V} {a b xm xp ym yp p q : V} {Km Kp : Finset V}

/-- The atoms of a (Y2) pair are not on a rung. -/
theorem RungCore.not_mem_pair (hR : RungCore C a b xm xp ym yp Km Kp) {p' q' : V}
    (hP : IsY2Pair C p q p' q') : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b := by
  have hpq := hP.mult_ab
  have hqp : C.mult s(q, p) = 3 := by rw [Sym2.eq_swap]; exact hpq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · rw [hR.mult_a] at hpq; split_ifs at hpq <;> omega
  · rw [hR.mult_b] at hpq; split_ifs at hpq <;> omega
  · rw [hR.mult_a] at hqp; split_ifs at hqp <;> omega
  · rw [hR.mult_b] at hqp; split_ifs at hqp <;> omega

/-- A neighbour of an atom of `Km` other than `a, b` lies in `Km`. -/
theorem RungCore.mem_Km_of_mult (hR : RungCore C a b xm xp ym yp Km Kp) {u w : V} (hu : u ∈ Km)
    (hw : C.mult s(u, w) ≠ 0) (hwa : w ≠ a) (hwb : w ≠ b) : w ∈ Km := by
  rcases hR.mem_poles (C.supp _ hw w (Sym2.mem_mk_right u w)) hwa hwb with h | h
  · exact h
  · exact absurd (hR.noBond u hu w h) hw

/-- The poles do not meet the rung. -/
theorem RungCore.ne_of_mem (hR : RungCore C a b xm xp ym yp Km Kp) {x : V} (hx : x ∈ Km ∨ x ∈ Kp) :
    x ≠ a ∧ x ≠ b := (hR.mem_verts hx).2

/-- Case (i): both externals in the pole. -/
theorem rung_case_i {p' q' : V} (hR : RungCore C a b xm xp ym yp Km Kp) (hP : IsY2Pair C p q p' q')
    (hp : p ∈ Km) (hq : q ∈ Km) (hp' : p' ∈ Km) (hq' : q' ∈ Km) (hpm : p ≠ xm) (hpm' : p ≠ ym)
    (hqm : q ≠ xm) (hqm' : q ≠ ym) (μ : Bool) :
    RungCore (y2Move C p q p' q') a b xm xp ym yp ((Km.erase p).erase q) Kp ∧
      IsY2Pair (rungDel C a b xm xp ym yp μ) p q p' q' ∧
      y2Move (rungDel C a b xm xp ym yp μ) p q p' q' = rungDel (y2Move C p q p' q') a b xm xp ym yp μ := by
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hpyp : p ≠ yp := fun h => hpP (h ▸ hR.yp_mem)
  have hqxp : q ≠ xp := fun h => hqP (h ▸ hR.xp_mem)
  have hqyp : q ≠ yp := fun h => hqP (h ▸ hR.yp_mem)
  obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (Or.inl hp)
  obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (Or.inl hq)
  obtain ⟨hp'a, hp'b⟩ := hR.ne_of_mem (Or.inl hp')
  obtain ⟨hq'a, hq'b⟩ := hR.ne_of_mem (Or.inl hq')
  have hC1 : RungCore (y2Move C p q p' q') a b xm xp ym yp ((Km.erase p).erase q) Kp := by
    refine ⟨hR.ne, fun x => ?_, fun x => ?_, ?_, ?_, ?_, ?_, hR.xp_mem, ?_, hR.yp_mem⟩
    · rw [y2Move_mult_far (Ne.symm hpa) (Ne.symm hqa) (Ne.symm hp'a) (Ne.symm hq'a), hR.mult_a]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]; rcases hx with rfl | rfl <;> simp [*]
      · rw [if_neg hx]
    · rw [y2Move_mult_far (Ne.symm hpb) (Ne.symm hqb) (Ne.symm hp'b) (Ne.symm hq'b), hR.mult_b]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]; rcases hx with rfl | rfl <;> simp [*]
      · rw [if_neg hx]
    · exact Finset.disjoint_of_subset_left
        ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hR.disj
    · rw [y2Move_verts hP]
      ext x
      have hu := Finset.ext_iff.mp hR.union x
      simp only [Finset.mem_union, Finset.mem_erase] at hu ⊢
      constructor
      · rintro (⟨hxq, hxp, hx⟩ | hx)
        · exact ⟨(hu.mp (Or.inl hx)).1, (hu.mp (Or.inl hx)).2.1, hxq, hxp, (hu.mp (Or.inl hx)).2.2⟩
        · refine ⟨(hu.mp (Or.inr hx)).1, (hu.mp (Or.inr hx)).2.1, ?_, ?_, (hu.mp (Or.inr hx)).2.2⟩
          · rintro rfl; exact hqP hx
          · rintro rfl; exact hpP hx
      · rintro ⟨hxb, hxa, hxq, hxp, hx⟩
        rcases hu.mpr ⟨hxb, hxa, hx⟩ with h | h
        · exact Or.inl ⟨hxq, hxp, h⟩
        · exact Or.inr h
    · intro u hu w hw
      simp only [Finset.mem_erase] at hu
      rw [y2Move_mult]
      have hne : s(u, w) ≠ s(p', q') := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact hR.not_mem_both hq' hw
        · exact hR.not_mem_both hp' hw
      split_ifs
      · rfl
      · simp [hR.noBond u hu.2.2 w hw, hne]
    · simp only [Finset.mem_erase]; exact ⟨fun h => hqm h.symm, fun h => hpm h.symm, hR.xm_mem⟩
    · simp only [Finset.mem_erase]; exact ⟨fun h => hqm' h.symm, fun h => hpm' h.symm, hR.ym_mem⟩
  have h2 : IsY2Pair (rungDel C a b xm xp ym yp μ) p q p' q' :=
    hP.congr (hR.rungDel_mult_inner hpa hpb hpm hpxp hpm' hpyp μ)
      (hR.rungDel_mult_inner hqa hqb hqm hqxp hqm' hqyp μ)
  refine ⟨hC1, h2, ext ?_ fun e => ?_⟩
  · rw [y2Move_verts h2, hR.verts_rungDel, hC1.verts_rungDel, y2Move_verts hP]
    ext x; simp only [Finset.mem_erase]; tauto
  · have hB1 : ∀ f ∈ ({s(p', q')} : Multiset (Sym2 V)), a ∉ f ∧ b ∉ f := by
      intro f hf
      rw [Multiset.mem_singleton] at hf
      subst hf
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hp'a, Ne.symm hq'a⟩, ⟨Ne.symm hp'b, Ne.symm hq'b⟩⟩
    have hB2 : ∀ f ∈ rungAdds xm xp ym yp μ, p ∉ f ∧ q ∉ f := fun f hf =>
      ⟨rungAdds_not_mem hpm hpxp hpm' hpyp μ f hf, rungAdds_not_mem hqm hqxp hqm' hqyp μ f hf⟩
    simp only [y2Move_eq_splice, rungDel]
    rw [splice_splice_mult _ _ _ hB1, splice_splice_mult _ _ _ hB2]
    by_cases h : p ∈ e ∨ q ∈ e ∨ a ∈ e ∨ b ∈ e
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]; ring

/-- Case (ii): `p = xm` with external `a`, and `q' ∈ Km`; `a`'s rail moves from `p` to `q'`. -/
theorem rung_case_ii {q' : V} (hR : RungCore C a b p xp ym yp Km Kp) (hP : IsY2Pair C p q a q')
    (hq : q ∈ Km) (hq' : q' ∈ Km) (hymp : ym ≠ p) (hymq : ym ≠ q) (μ : Bool) :
    RungCore (y2Move C p q a q') a b q' xp ym yp ((Km.erase p).erase q) Kp ∧
      IsY2Pair (rungDel C a b p xp ym yp μ) p q (if μ then yp else xp) q' ∧
      y2Move (rungDel C a b p xp ym yp μ) p q (if μ then yp else xp) q' =
        rungDel (y2Move C p q a q') a b q' xp ym yp μ := by
  have hp := hR.xm_mem
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hq'P : q' ∉ Kp := fun h => hR.not_mem_both hq' h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hpyp : p ≠ yp := fun h => hpP (h ▸ hR.yp_mem)
  have hqxp : q ≠ xp := fun h => hqP (h ▸ hR.xp_mem)
  have hqyp : q ≠ yp := fun h => hqP (h ▸ hR.yp_mem)
  have hq'xp : q' ≠ xp := fun h => hq'P (h ▸ hR.xp_mem)
  have hq'yp : q' ≠ yp := fun h => hq'P (h ▸ hR.yp_mem)
  obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (Or.inl hp)
  obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (Or.inl hq)
  obtain ⟨hq'a, hq'b⟩ := hR.ne_of_mem (Or.inl hq')
  have hq'p : q' ≠ p := hP.d_ne_a
  have hq'q : q' ≠ q := hP.d_ne_b
  have hC1 : RungCore (y2Move C p q a q') a b q' xp ym yp ((Km.erase p).erase q) Kp := by
    refine ⟨hR.ne, fun x => ?_, fun x => ?_, ?_, ?_, ?_, ?_, hR.xp_mem, ?_, hR.yp_mem⟩
    · rw [y2Move_mult_ext (Ne.symm hpa) (Ne.symm hqa), hR.mult_a]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]; rcases hx with rfl | rfl <;> simp [*, Ne.symm hq'p, Ne.symm hq'q]
      · rw [if_neg hx]
        have hxp : x ≠ p := fun h => hx (Or.inl h)
        by_cases hxb : x = b
        · subst hxb; simp [Ne.symm hq'b]
        · by_cases hxq' : x = q'
          · subst hxq'; simp [hxb, hxp, hq'xp]
          · by_cases hxx : x = xp
            · subst hxx; simp [hxb, hxp, hxq']
            · simp [hxb, hxp, hxq', hxx]
    · rw [y2Move_mult_far (Ne.symm hpb) (Ne.symm hqb) hR.ne.symm (Ne.symm hq'b), hR.mult_b]
      by_cases hx : x = p ∨ x = q
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [*, Ne.symm hymp, Ne.symm hymq]
      · rw [if_neg hx]
    · exact Finset.disjoint_of_subset_left
        ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hR.disj
    · rw [y2Move_verts hP]
      ext x
      have hu := Finset.ext_iff.mp hR.union x
      simp only [Finset.mem_union, Finset.mem_erase] at hu ⊢
      constructor
      · rintro (⟨hxq, hxp, hx⟩ | hx)
        · exact ⟨(hu.mp (Or.inl hx)).1, (hu.mp (Or.inl hx)).2.1, hxq, hxp, (hu.mp (Or.inl hx)).2.2⟩
        · refine ⟨(hu.mp (Or.inr hx)).1, (hu.mp (Or.inr hx)).2.1, ?_, ?_, (hu.mp (Or.inr hx)).2.2⟩
          · rintro rfl; exact hqP hx
          · rintro rfl; exact hpP hx
      · rintro ⟨hxb, hxa, hxq, hxp, hx⟩
        rcases hu.mpr ⟨hxb, hxa, hx⟩ with h | h
        · exact Or.inl ⟨hxq, hxp, h⟩
        · exact Or.inr h
    · intro u hu w hw
      simp only [Finset.mem_erase] at hu
      rw [y2Move_mult]
      have hne : s(u, w) ≠ s(a, q') := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact (hR.ne_of_mem (Or.inl hu.2.2)).1 h1
        · exact (hR.ne_of_mem (Or.inr hw)).1 h2
      split_ifs
      · rfl
      · simp [hR.noBond u hu.2.2 w hw, hne]
    · simp only [Finset.mem_erase]; exact ⟨hq'q, hq'p, hq'⟩
    · simp only [Finset.mem_erase]; exact ⟨hymq, hymp, hR.ym_mem⟩
  -- the external of `p` after the deletion
  set z := if μ then yp else xp with hz
  have hzK : z ∈ Kp := by cases μ <;> simp [hz, hR.xp_mem, hR.yp_mem]
  have hzp : z ≠ p := fun h => hpP (h ▸ hzK)
  have hzq : z ≠ q := fun h => hqP (h ▸ hzK)
  have hzq' : z ≠ q' := fun h => hq'P (h ▸ hzK)
  obtain ⟨hza, hzb⟩ := hR.ne_of_mem (Or.inr hzK)
  have hcountp : ∀ x, (rungAdds p xp ym yp μ).count s(p, x) = if x = z then 1 else 0 := by
    intro x
    cases μ
    · simp only [hz, rungAdds, Bool.false_eq_true, if_false, count_pair, Sym2.congr_right]
      have : s(p, x) ≠ s(ym, yp) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hymp h1.symm, hpyp h1]
      rw [if_neg this, add_zero]
    · simp only [hz, rungAdds, if_true, count_pair, Sym2.congr_right]
      have : s(p, x) ≠ s(xp, ym) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hpxp h1, hymp h1.symm]
      rw [if_neg this, add_zero]
  have h2 : IsY2Pair (rungDel C a b p xp ym yp μ) p q z q' := by
    refine IsY2Pair.of_mult hP.ne hzq' hzp hzq hq'p hq'q (fun x => ?_) (fun x => ?_)
    · rw [rungDel, splice_mult_at _ _ hpa hpb, hP.mult_a, hcountp]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]; rcases hx with rfl | rfl <;> simp [Ne.symm hqa, Ne.symm hqb, Ne.symm hza, Ne.symm hzb]
      · rw [if_neg hx]
        have hxa : x ≠ a := fun h => hx (Or.inl h)
        by_cases hxq : x = q
        · subst hxq; simp [hzq.symm]
        · simp [hxq, hxa]
    · rw [hR.rungDel_mult_inner hqa hqb (fun h => hP.ne h.symm) hqxp (fun h => hymq h.symm) hqyp μ,
        hP.mult_b]
  refine ⟨hC1, h2, ext ?_ fun e => ?_⟩
  · rw [y2Move_verts h2, hR.verts_rungDel, hC1.verts_rungDel, y2Move_verts hP]
    ext x; simp only [Finset.mem_erase]; tauto
  · have hB1 : ∀ f ∈ ({s(z, q')} : Multiset (Sym2 V)), a ∉ f ∧ b ∉ f := by
      intro f hf
      rw [Multiset.mem_singleton] at hf
      subst hf
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hza, Ne.symm hq'a⟩, ⟨Ne.symm hzb, Ne.symm hq'b⟩⟩
    have hB2 : ∀ f ∈ rungAdds q' xp ym yp μ, p ∉ f ∧ q ∉ f := fun f hf =>
      ⟨rungAdds_not_mem (fun h => hq'p h.symm) hpxp (fun h => hymp h.symm) hpyp μ f hf,
        rungAdds_not_mem (fun h => hq'q h.symm) hqxp (fun h => hymq h.symm) hqyp μ f hf⟩
    simp only [y2Move_eq_splice, rungDel]
    rw [splice_splice_mult _ _ _ hB1, splice_splice_mult _ _ _ hB2]
    by_cases h : p ∈ e ∨ q ∈ e ∨ a ∈ e ∨ b ∈ e
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
      have hpe : p ∉ e := fun h' => h (Or.inl h')
      have hae : a ∉ e := fun h' => h (Or.inr (Or.inr (Or.inl h')))
      have e1 : e ≠ s(a, q') := fun h' => hae (h' ▸ Sym2.mem_mk_left a q')
      have e2 : e ≠ s(p, yp) := fun h' => hpe (h' ▸ Sym2.mem_mk_left p yp)
      have e3 : e ≠ s(p, xp) := fun h' => hpe (h' ▸ Sym2.mem_mk_left p xp)
      cases μ
      · simp only [hz, rungAdds, Bool.false_eq_true, if_false, count_pair, Multiset.count_singleton, e1, e3,
          Sym2.eq_swap (a := xp) (b := q')]
        ring
      · simp only [hz, rungAdds, if_true, count_pair, Multiset.count_singleton, e1, e2,
          Sym2.eq_swap (a := yp) (b := q')]
        ring

end Cases

end WaveTurbulence.TVine.Core

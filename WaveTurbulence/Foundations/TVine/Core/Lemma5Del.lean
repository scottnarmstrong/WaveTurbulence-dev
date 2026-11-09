/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma5

/-!
# Lemma 5′: rung deletion as path surgery (M4 §5.3; REF-M4 claim 5)

`y2Path_deleteRung`: if `R = {a, b}` carries rung data (`RungCore`, in particular any 2-cut rung, `IsRungAt.toCore`)
and `C →* T'` along `ps` with `T'` a doubled triangle, then `R` occurs exactly once in `ps`, and for either matching
`μ`, `C/[μ]R →* T'` along `ps.erase R`.

Case (iii) of M4 (the pole collapses) is `rung_case_iii`, which hands over to Lemma E.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

section Cases

variable {C : UMultigraph V} {a b xp yp p q : V} {Km Kp : Finset V}

/-- Case (iii): `P = {xm, ym}` with externals `a, b`; the pole collapses onto the rung. -/
theorem rung_case_iii (hR : RungCore C a b p xp q yp Km Kp) (hP : IsY2Pair C p q a b) :
    (xp = yp → Stuck (y2Move C p q a b) a b 3 xp) ∧
    (xp ≠ yp → IsY2Pair (y2Move C p q a b) a b xp yp ∧ ∀ μ : Bool,
      IsY2Pair (rungDel C a b p xp q yp μ) p q (if μ then yp else xp) (if μ then xp else yp) ∧
      y2Move (rungDel C a b p xp q yp μ) p q (if μ then yp else xp) (if μ then xp else yp) =
        y2Move (y2Move C p q a b) a b xp yp) := by
  have hp := hR.xm_mem
  have hq := hR.ym_mem
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hpyp : p ≠ yp := fun h => hpP (h ▸ hR.yp_mem)
  have hqxp : q ≠ xp := fun h => hqP (h ▸ hR.xp_mem)
  have hqyp : q ≠ yp := fun h => hqP (h ▸ hR.yp_mem)
  obtain ⟨hpa, hpb⟩ := hR.ne_of_mem (Or.inl hp)
  obtain ⟨hqa, hqb⟩ := hR.ne_of_mem (Or.inl hq)
  obtain ⟨hxpa, hxpb⟩ := hR.ne_of_mem (Or.inr hR.xp_mem)
  obtain ⟨hypa, hypb⟩ := hR.ne_of_mem (Or.inr hR.yp_mem)
  have hpq := hP.ne
  have ha : ∀ x, (y2Move C p q a b).mult s(a, x) = if x = b then 3 else if x = xp then 1 else 0 := by
    intro x
    rw [y2Move_mult_ext (Ne.symm hpa) (Ne.symm hqa), hR.mult_a]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hpb, hqb, hpxp, hqxp]
    · rw [if_neg hx]
      have hxp : x ≠ p := fun h => hx (Or.inl h)
      by_cases hxb : x = b
      · subst hxb; simp
      · by_cases hxx : x = xp
        · subst hxx; simp [hxb, hxp]
        · simp [hxb, hxp, hxx]
  have hb : ∀ x, (y2Move C p q a b).mult s(b, x) = if x = a then 3 else if x = yp then 1 else 0 := by
    intro x
    rw [y2Move_mult_ext' (Ne.symm hpb) (Ne.symm hqb), hR.mult_b]
    by_cases hx : x = p ∨ x = q
    · rw [if_pos hx]
      rcases hx with rfl | rfl <;> simp [hpa, hqa, hpyp, hqyp]
    · rw [if_neg hx]
      have hxq : x ≠ q := fun h => hx (Or.inr h)
      by_cases hxa : x = a
      · subst hxa; simp
      · by_cases hxy : x = yp
        · subst hxy; simp [hxa, hxq]
        · simp [hxa, hxq, hxy]
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · subst hxy
    exact ⟨hR.ne, hxpa, hxpb, le_refl 3, by omega, ha, hb⟩
  have h1 : IsY2Pair (y2Move C p q a b) a b xp yp :=
    IsY2Pair.of_mult hR.ne hxy hxpa hxpb hypa hypb ha hb
  refine ⟨h1, fun μ => ?_⟩
  set z₁ := if μ then yp else xp with hz₁
  set z₂ := if μ then xp else yp with hz₂
  have hz₁K : z₁ ∈ Kp := by cases μ <;> simp [hz₁, hR.xp_mem, hR.yp_mem]
  have hz₂K : z₂ ∈ Kp := by cases μ <;> simp [hz₂, hR.xp_mem, hR.yp_mem]
  have hz : z₁ ≠ z₂ := by cases μ <;> simp [hz₁, hz₂, hxy, Ne.symm hxy]
  obtain ⟨hz₁a, hz₁b⟩ := hR.ne_of_mem (Or.inr hz₁K)
  obtain ⟨hz₂a, hz₂b⟩ := hR.ne_of_mem (Or.inr hz₂K)
  have hcp : ∀ x, (rungAdds p xp q yp μ).count s(p, x) = if x = z₁ then 1 else 0 := by
    intro x
    cases μ
    · simp only [hz₁, rungAdds, Bool.false_eq_true, if_false, count_pair, Sym2.congr_right]
      have : s(p, x) ≠ s(q, yp) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hpq h1, hpyp h1]
      rw [if_neg this, add_zero]
    · simp only [hz₁, rungAdds, if_true, count_pair, Sym2.congr_right]
      have : s(p, x) ≠ s(xp, q) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hpxp h1, hpq h1]
      rw [if_neg this, add_zero]
  have hcq : ∀ x, (rungAdds p xp q yp μ).count s(q, x) = if x = z₂ then 1 else 0 := by
    intro x
    cases μ
    · simp only [hz₂, rungAdds, Bool.false_eq_true, if_false, count_pair, Sym2.congr_right]
      have : s(q, x) ≠ s(p, xp) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hpq h1.symm, hqxp h1]
      rw [if_neg this, zero_add]
    · simp only [hz₂, rungAdds, if_true, count_pair, Sym2.eq_swap (a := xp) (b := q), Sym2.congr_right]
      have : s(q, x) ≠ s(p, yp) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hpq h1.symm, hqyp h1]
      rw [if_neg this, zero_add]
  have h2 : IsY2Pair (rungDel C a b p xp q yp μ) p q z₁ z₂ := by
    refine IsY2Pair.of_mult hpq hz (fun h => hpP (h ▸ hz₁K)) (fun h => hqP (h ▸ hz₁K))
      (fun h => hpP (h ▸ hz₂K)) (fun h => hqP (h ▸ hz₂K)) (fun x => ?_) (fun x => ?_)
    · rw [rungDel, splice_mult_at _ _ hpa hpb, hP.mult_a, hcp]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [Ne.symm hqa, Ne.symm hqb, Ne.symm hz₁a, Ne.symm hz₁b]
      · rw [if_neg hx]
        have hxa : x ≠ a := fun h => hx (Or.inl h)
        by_cases hxq : x = q
        · have hqz : q ≠ z₁ := fun h => hqP (h ▸ hz₁K)
          rw [hxq]; simp [hqz]
        · simp [hxq, hxa]
    · rw [rungDel, splice_mult_at _ _ hqa hqb, hP.mult_b, hcq]
      by_cases hx : x = a ∨ x = b
      · rw [if_pos hx]
        rcases hx with rfl | rfl <;> simp [Ne.symm hpa, Ne.symm hpb, Ne.symm hz₂a, Ne.symm hz₂b]
      · rw [if_neg hx]
        have hxb : x ≠ b := fun h => hx (Or.inr h)
        by_cases hxp : x = p
        · have hpz : p ≠ z₂ := fun h => hpP (h ▸ hz₂K)
          rw [hxp]; simp [hpz]
        · simp [hxp, hxb]
  refine ⟨h2, ext ?_ fun e => ?_⟩
  · rw [y2Move_verts h2, hR.verts_rungDel, y2Move_verts h1, y2Move_verts hP]
    ext x; simp only [Finset.mem_erase]; tauto
  · have hB1 : ∀ f ∈ ({s(z₁, z₂)} : Multiset (Sym2 V)), a ∉ f ∧ b ∉ f := by
      intro f hf
      rw [Multiset.mem_singleton] at hf
      subst hf
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hz₁a, Ne.symm hz₂a⟩, ⟨Ne.symm hz₁b, Ne.symm hz₂b⟩⟩
    rw [y2Move_y2Move_mult h1]
    simp only [y2Move_eq_splice, rungDel]
    rw [splice_splice_mult _ _ _ hB1]
    by_cases h : p ∈ e ∨ q ∈ e ∨ a ∈ e ∨ b ∈ e
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
      have hpe : p ∉ e := fun h' => h (Or.inl h')
      have hqe : q ∉ e := fun h' => h (Or.inr (Or.inl h'))
      have hae : a ∉ e := fun h' => h (Or.inr (Or.inr (Or.inl h')))
      have e0 : e ≠ s(a, b) := fun h' => hae (h' ▸ Sym2.mem_mk_left a b)
      have e1 : e ≠ s(p, yp) := fun h' => hpe (h' ▸ Sym2.mem_mk_left p yp)
      have e2 : e ≠ s(p, xp) := fun h' => hpe (h' ▸ Sym2.mem_mk_left p xp)
      have e3 : e ≠ s(xp, q) := fun h' => hqe (h' ▸ Sym2.mem_mk_right xp q)
      have e4 : e ≠ s(q, yp) := fun h' => hqe (h' ▸ Sym2.mem_mk_left q yp)
      cases μ
      · simp only [hz₁, hz₂, rungAdds, Bool.false_eq_true, if_false, count_pair, Multiset.count_singleton,
          e0, e2, e4, ↓reduceIte, add_zero]
      · simp only [hz₁, hz₂, rungAdds, if_true, count_pair, Multiset.count_singleton, e0, e1, e3,
          Sym2.eq_swap (a := yp) (b := xp), ↓reduceIte, add_zero]

end Cases

/-! ## Lemma 5′ -/

section Main

variable {C T' : UMultigraph V} {a b xm xp ym yp p q p' q' : V} {Km Kp : Finset V} {rest : List (Sym2 V)}

/-- The induction hypothesis of Lemma 5′ at the graph after the first move. -/
def DelIH (C T' : UMultigraph V) (rest : List (Sym2 V)) : Prop :=
  ∀ {a b xm xp ym yp : V} {Km Kp : Finset V} (μ : Bool), RungCore C a b xm xp ym yp Km Kp →
    rest.count s(a, b) = 1 ∧ Y2Path (rungDel C a b xm xp ym yp μ) (rest.erase s(a, b)) T'

/-- The three normalised cases, for a first move inside `Km`. -/
private theorem delete_core (μ : Bool) (hT : IsDoubledTriangle T') (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair C p q p' q') (hp : p ∈ Km) (hq : q ∈ Km)
    (hcase : (p' ≠ a ∧ p' ≠ b ∧ q' ≠ a ∧ q' ≠ b) ∨ (p' = a ∧ q' ≠ a ∧ q' ≠ b) ∨ (p' = a ∧ q' = b))
    (hrest : Y2Path (y2Move C p q p' q') rest T') (ih : DelIH (y2Move C p q p' q') T' rest) :
    (s(p, q) :: rest).count s(a, b) = 1 ∧
      Y2Path (rungDel C a b xm xp ym yp μ) ((s(p, q) :: rest).erase s(a, b)) T' := by
  obtain ⟨hpa, hpb, hqa, hqb⟩ := hR.not_mem_pair hP
  have hne : s(p, q) ≠ s(a, b) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    exacts [hpa h1, hpb h1]
  have hpP : p ∉ Kp := fun h => hR.not_mem_both hp h
  have hqP : q ∉ Kp := fun h => hR.not_mem_both hq h
  have hpxp : p ≠ xp := fun h => hpP (h ▸ hR.xp_mem)
  have hqyp : q ≠ yp := fun h => hqP (h ▸ hR.yp_mem)
  rcases hcase with ⟨hp'a, hp'b, hq'a, hq'b⟩ | ⟨hp'a, hq'a, hq'b⟩ | ⟨hp'a, hq'b⟩
  · -- (i)
    have hp' : p' ∈ Km := hR.mem_Km_of_mult hp (by rw [hP.mult_ac]; omega) hp'a hp'b
    have hq' : q' ∈ Km := hR.mem_Km_of_mult hq (by rw [hP.mult_bd]; omega) hq'a hq'b
    have hpm : p ≠ xm := by
      intro h; have h1 := hR.mult_a p
      rw [Sym2.eq_swap, hP.a_other a (Ne.symm hqa) (Ne.symm hp'a), if_neg hpb, if_pos (Or.inl h)] at h1
      omega
    have hpm' : p ≠ ym := by
      intro h; have h1 := hR.mult_b p
      rw [Sym2.eq_swap, hP.a_other b (Ne.symm hqb) (Ne.symm hp'b), if_neg hpa, if_pos (Or.inl h)] at h1
      omega
    have hqm : q ≠ xm := by
      intro h; have h1 := hR.mult_a q
      rw [Sym2.eq_swap, hP.b_other a (Ne.symm hpa) (Ne.symm hq'a), if_neg hqb, if_pos (Or.inl h)] at h1
      omega
    have hqm' : q ≠ ym := by
      intro h; have h1 := hR.mult_b q
      rw [Sym2.eq_swap, hP.b_other b (Ne.symm hpb) (Ne.symm hq'b), if_neg hqa, if_pos (Or.inl h)] at h1
      omega
    obtain ⟨h1, h2, h3⟩ := rung_case_i hR hP hp hq hp' hq' hpm hpm' hqm hqm' μ
    exact cons_assemble hne h2 h3 (ih μ h1)
  · -- (ii)
    subst p'
    have hpm : p = xm := by
      have h1 := hR.mult_a p
      rw [Sym2.eq_swap, hP.mult_ac, if_neg hpb] at h1
      by_contra hpm
      rw [if_neg (by rintro (h | h); exacts [hpm h, hpxp h])] at h1
      omega
    subst xm
    have hq' : q' ∈ Km := hR.mem_Km_of_mult hq (by rw [hP.mult_bd]; omega) hq'a hq'b
    have hymp : ym ≠ p := by
      intro h; have h1 := hR.mult_b p
      rw [Sym2.eq_swap, hP.a_other b (Ne.symm hqb) hR.ne.symm, if_neg hpa, if_pos (Or.inl h.symm)] at h1
      omega
    have hymq : ym ≠ q := by
      intro h; have h1 := hR.mult_b q
      rw [Sym2.eq_swap, hP.b_other b (Ne.symm hpb) (Ne.symm hq'b), if_neg hqa, if_pos (Or.inl h.symm)] at h1
      omega
    obtain ⟨h1, h2, h3⟩ := rung_case_ii hR hP hq hq' hymp hymq μ
    exact cons_assemble hne h2 h3 (ih μ h1)
  · -- (iii)
    subst p'; subst q'
    have hpm : p = xm := by
      have h1 := hR.mult_a p
      rw [Sym2.eq_swap, hP.mult_ac, if_neg hpb] at h1
      by_contra hpm
      rw [if_neg (by rintro (h | h); exacts [hpm h, hpxp h])] at h1
      omega
    have hqm : q = ym := by
      have h1 := hR.mult_b q
      rw [Sym2.eq_swap, hP.mult_bd, if_neg hqa] at h1
      by_contra hqm
      rw [if_neg (by rintro (h | h); exacts [hqm h, hqyp h])] at h1
      omega
    subst xm; subst ym
    by_cases hxy : xp = yp
    · exact (((rung_case_iii hR hP).1 hxy).not_y2Path hrest hT).elim
    · obtain ⟨h1, h2⟩ := (rung_case_iii hR hP).2 hxy
      obtain ⟨h3, h4⟩ := h2 μ
      exact cons_assemble hne h3 h4 (y2Path_early hrest hT h1)

/-- A first move inside `Km` whose externals are not `(∉ R, ∈ R)`: normalise `a ↔ b`. -/
private theorem delete_km1 (μ : Bool) (hT : IsDoubledTriangle T') (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair C p q p' q') (hp : p ∈ Km) (hq : q ∈ Km) (hpre : (p' = a ∨ p' = b) ∨ (q' ≠ a ∧ q' ≠ b))
    (hrest : Y2Path (y2Move C p q p' q') rest T') (ih : DelIH (y2Move C p q p' q') T' rest) :
    (s(p, q) :: rest).count s(a, b) = 1 ∧
      Y2Path (rungDel C a b xm xp ym yp μ) ((s(p, q) :: rest).erase s(a, b)) T' := by
  have hp'q' := hP.ext_ne
  by_cases hp'b : p' = b
  · -- swap `a ↔ b`
    have hcase : (p' ≠ b ∧ p' ≠ a ∧ q' ≠ b ∧ q' ≠ a) ∨ (p' = b ∧ q' ≠ b ∧ q' ≠ a) ∨ (p' = b ∧ q' = a) := by
      by_cases hq'a : q' = a
      · exact Or.inr (Or.inr ⟨hp'b, hq'a⟩)
      · exact Or.inr (Or.inl ⟨hp'b, fun h => hp'q' (hp'b.trans h.symm), hq'a⟩)
    have := delete_core μ hT hR.swapAB hP hp hq hcase hrest ih
    rwa [show s(b, a) = s(a, b) from Sym2.eq_swap, ← rungDel_swapAB] at this
  · have hcase : (p' ≠ a ∧ p' ≠ b ∧ q' ≠ a ∧ q' ≠ b) ∨ (p' = a ∧ q' ≠ a ∧ q' ≠ b) ∨ (p' = a ∧ q' = b) := by
      by_cases hp'a : p' = a
      · by_cases hq'b : q' = b
        · exact Or.inr (Or.inr ⟨hp'a, hq'b⟩)
        · exact Or.inr (Or.inl ⟨hp'a, fun h => hp'q' (hp'a.trans h.symm), hq'b⟩)
      · rcases hpre with h | h
        · exact absurd h (by tauto)
        · exact Or.inl ⟨hp'a, hp'b, h⟩
    exact delete_core μ hT hR hP hp hq hcase hrest ih

/-- A first move inside `Km`: normalise the orientation of `P`. -/
private theorem delete_km (μ : Bool) (hT : IsDoubledTriangle T') (hR : RungCore C a b xm xp ym yp Km Kp)
    (hP : IsY2Pair C p q p' q') (hp : p ∈ Km) (hq : q ∈ Km)
    (hrest : Y2Path (y2Move C p q p' q') rest T') (ih : DelIH (y2Move C p q p' q') T' rest) :
    (s(p, q) :: rest).count s(a, b) = 1 ∧
      Y2Path (rungDel C a b xm xp ym yp μ) ((s(p, q) :: rest).erase s(a, b)) T' := by
  by_cases hsw : (p' ≠ a ∧ p' ≠ b) ∧ (q' = a ∨ q' = b)
  · have hrest' : Y2Path (y2Move C q p q' p') rest T' := by rw [y2Move_swap C p q p' q']; exact hrest
    have ih' : DelIH (y2Move C q p q' p') T' rest := by rw [y2Move_swap C p q p' q']; exact ih
    have := delete_km1 μ hT hR hP.swap hq hp (Or.inl hsw.2) hrest' ih'
    rwa [show s(q, p) = s(p, q) from Sym2.eq_swap] at this
  · have hpre : (p' = a ∨ p' = b) ∨ (q' ≠ a ∧ q' ≠ b) := by tauto
    exact delete_km1 μ hT hR hP hp hq hpre hrest ih

/-- **Lemma 5′** (M4 §5.3; REF-M4 claim 5): rung deletion as path surgery. If `R = {a, b}` carries rung data and
`C →* T'` (a doubled triangle) along `ps`, then `R` occurs exactly once in `ps`, and for either matching `μ`,
`C/[μ]R →* T'` along `ps` with that move deleted. -/
theorem y2Path_deleteRung {ps : List (Sym2 V)} (hp : Y2Path C ps T') (hT : IsDoubledTriangle T')
    (hR : RungCore C a b xm xp ym yp Km Kp) (μ : Bool) :
    ps.count s(a, b) = 1 ∧ Y2Path (rungDel C a b xm xp ym yp μ) (ps.erase s(a, b)) T' := by
  induction hp generalizing a b xm xp ym yp Km Kp μ with
  | nil G => exact (hR.not_doubledTriangle hT).elim
  | @cons C T' p q p' q' rest hP hrest ih =>
    replace ih : DelIH (y2Move C p q p' q') T' rest := fun μ h => by
      first | exact ih hT h μ | exact ih h μ hT | exact ih h hT μ
    obtain ⟨hpa, hpb, hqa, hqb⟩ := hR.not_mem_pair hP
    rcases hR.mem_poles hP.a_mem hpa hpb with hp | hp
    · have hq : q ∈ Km := hR.mem_Km_of_mult hp (by rw [hP.mult_ab]; omega) hqa hqb
      exact delete_km μ hT hR hP hp hq hrest ih
    · have hq : q ∈ Kp := hR.swapPoles.mem_Km_of_mult hp (by rw [hP.mult_ab]; omega) hqa hqb
      have := delete_km μ hT hR.swapPoles hP hp hq hrest ih
      rwa [← rungDel_swapPoles] at this

end Main

end WaveTurbulence.TVine.Core

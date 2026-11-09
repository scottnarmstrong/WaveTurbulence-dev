/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.TCap

/-!
# Deleting a cap rung of a T-vine (N3 §2.1 (ii), second bullet)

A rung `R = {a, b}` of a T-vine `X` (joints `p, q`, rung atoms not joints) whose pole `K⁻` consists of joints only.
After orienting, `K⁻ ⊆ {p, q}` and `xm = p`; then either

* (A) `ym = p`: the joint `p` carries both rails, `nbrs p = {a, b}`; or
* (B) `ym = q`: `K⁻ = {p, q}`, `nbrs p = {a, q}`, `nbrs q = {b, p}`.

In both cases the rung pair is a triple pair of the closure `C` of `X` (if its two externals coincided, or it had
none, it would be stuck and `C` could not reduce to `T`), and the closure of `X/[μ]R` is the (Y2) move of `C` at
that pair (`isClosureU_y2Move`); Lemma 1.5 (cap case, `reducesToT_y2Move_iff`) transfers the reduction.

* `isTVineU_rungDel_cap`: a cap rung of a T-vine (given by rung data) can be deleted, either matching;
* `isTVineU_rungDel_any`: any rung of a T-vine (given by rung data, rung atoms not joints) can be deleted.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section Cap

variable {X : UMultigraph V} {p q a b xp yp : V} {Km Kp : Finset V}

/-! ## Case (A): one joint carries both rails -/

/-- The common data of case (A). -/
theorem capA_setup (hT : IsTVineU X p q) (hR : RungCore X a b p xp p yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) :
    X.Loopless ∧ nbrs X p = {a, b} ∧ X.mult s(p, q) = 0 ∧ deg X q = 2 ∧ p ≠ q ∧ p ∈ X.verts ∧ q ∈ X.verts ∧
      ∃ (C : UMultigraph V) (c' d' : V), nbrs X q = {c', d'} ∧ C.verts = (X.verts.erase p).erase q ∧
        C.Loopless ∧ ReducesToT C ∧
        ∀ e, C.mult e = (if p ∈ e ∨ q ∈ e then 0 else X.mult e) +
          ({s(a, b), s(c', d')} : Multiset (Sym2 V)).count e := by
  have hl := hT.loopless
  obtain ⟨⟨hpV, hqV, hpq, hdp, hdq, -, -⟩, -, C, ⟨-, hCV, hCl, added, hdata, hCm⟩, hRT⟩ := hT
  have hNp : nbrs X p = {a, b} :=
    nbrs_eq_of_two hdp ((hR.mem_nbrs_of_rail (Ne.symm hap) (Ne.symm hbp)).1 (Or.inl rfl))
      ((hR.mem_nbrs_of_rail (Ne.symm hap) (Ne.symm hbp)).2 (Or.inl rfl)) hR.ne
  have hσ : X.mult s(p, q) = 0 := by
    rw [mult_of_nbrs_eq hNp (Ne.symm hpq), count_pair_v, if_neg (Ne.symm haq), if_neg (Ne.symm hbq)]
  refine ⟨hl, hNp, hσ, hdq, hpq, hpV, hqV, ?_⟩
  rcases hdata with ⟨-, a', b', c', d', h1, h2, rfl⟩ | ⟨h1, -⟩
  · refine ⟨C, c', d', h2, hCV, hCl, hRT, fun e => ?_⟩
    rw [hCm, sym2_eq_of_pair_eq (h1.symm.trans hNp)]
  · omega

/-- Case (A) with both rails of the other side ending at the second joint is impossible (stuck pair). -/
theorem capA_stuck (hT : IsTVineU X p q) (hR : RungCore X a b p xp p yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hqx : q = xp) (hqy : q = yp) : False := by
  obtain ⟨-, -, -, hdq, -, -, -, C, c', d', hNq, -, -, hRT, hCm⟩ := capA_setup hT hR hap haq hbp hbq
  have hNq' : nbrs X q = {a, b} :=
    nbrs_eq_of_two hdq ((hR.mem_nbrs_of_rail (Ne.symm haq) (Ne.symm hbq)).1 (Or.inr hqx))
      ((hR.mem_nbrs_of_rail (Ne.symm haq) (Ne.symm hbq)).2 (Or.inr hqy)) hR.ne
  rw [sym2_eq_of_pair_eq (hNq.symm.trans hNq')] at hCm
  have ha : ∀ x, C.mult s(a, x) = if x = b then 4 else if x = p then 4 - 4 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hap) (Ne.symm haq) hCm hR.mult_a x, count_pair, ind_left, ← hqx]
    exact rail_closed4 hbp hbq
  have hb : ∀ x, C.mult s(b, x) = if x = a then 4 else if x = p then 4 - 4 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hbp) (Ne.symm hbq) hCm hR.mult_b x, count_pair, ind_right, ← hqy]
    exact rail_closed4 hap haq
  exact not_reducesToT_of_stuck ⟨hR.ne, Ne.symm hap, Ne.symm hbp, by norm_num, le_refl _, ha, hb⟩ hRT

/-- Case (A1): the second joint is not adjacent to the rung. -/
theorem capA1 (hT : IsTVineU X p q) (hR : RungCore X a b p xp p yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hqx : q ≠ xp) (hqy : q ≠ yp) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b p xp p yp μ) p q C' ∧ ReducesToT C' := by
  obtain ⟨hl, hNp, hσ, -, hpq, -, -, C, c', d', hNq, hCV, hCl, hRT, hCm⟩ := capA_setup hT hR hap haq hbp hbq
  have hpK := hR.xm_mem
  have hxpK := hR.xp_mem
  have hypK := hR.yp_mem
  have hxpp : xp ≠ p := fun h => hR.not_mem_both hpK (h ▸ hxpK)
  have hypp : yp ≠ p := fun h => hR.not_mem_both hpK (h ▸ hypK)
  obtain ⟨hxpV, hxpa, hxpb⟩ := hR.mem_verts (Or.inr hxpK)
  obtain ⟨hypV, hypa, hypb⟩ := hR.mem_verts (Or.inr hypK)
  have hcdV := nbrs_mem_verts hNq
  have hcdq := nbrs_mem_ne hl hNq
  -- `q` is not adjacent to `a`, `b`, `p`
  have hXqa : X.mult s(q, a) = 0 := by
    rw [Sym2.eq_swap, hR.mult_a, if_neg (Ne.symm hbq), if_neg]
    rintro (h | h); exacts [hpq h.symm, hqx h]
  have hXqb : X.mult s(q, b) = 0 := by
    rw [Sym2.eq_swap, hR.mult_b, if_neg (Ne.symm haq), if_neg]
    rintro (h | h); exacts [hpq h.symm, hqy h]
  have hXqp : X.mult s(q, p) = 0 := by rw [Sym2.eq_swap]; exact hσ
  obtain ⟨hca, hda⟩ := pair_ne_of_count ((mult_of_nbrs_eq hNq haq).symm.trans hXqa)
  obtain ⟨hcb, hdb⟩ := pair_ne_of_count ((mult_of_nbrs_eq hNq hbq).symm.trans hXqb)
  obtain ⟨hcp, hdp⟩ := pair_ne_of_count ((mult_of_nbrs_eq hNq hpq).symm.trans hXqp)
  -- the rung pair is a (Y2) pair of the closure
  have hCa : ∀ x, C.mult s(a, x) = if x = b then 3 else if x = xp then 1 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hap) (Ne.symm haq) hCm hR.mult_a x, count_pair, ind_left,
      if_neg (sym2_ne_of (Ne.symm hca) (Ne.symm hda)), add_zero]
    exact rail_closed (Or.inl rfl) hbp hbq hxpp (Ne.symm hqx)
  have hCb : ∀ x, C.mult s(b, x) = if x = a then 3 else if x = yp then 1 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hbp) (Ne.symm hbq) hCm hR.mult_b x, count_pair, ind_right,
      if_neg (sym2_ne_of (Ne.symm hcb) (Ne.symm hdb)), add_zero]
    exact rail_closed (Or.inl rfl) hap haq hypp (Ne.symm hqy)
  have hQ := y2Pair_of_reducesToT hR.ne hxpa hxpb hypa hypb hCa hCb hRT
  -- the joints of the deleted graph
  have hZV := hR.verts_rungDel μ
  have hA := rungAdds_capA p xp yp μ
  have hNpZ : nbrs (rungDel X a b p xp p yp μ) p = {xp, yp} := by
    apply nbrs_splice_of (Ne.symm hap) (Ne.symm hbp) hNp (hl p) (hR.rungAdds_count_diag μ p) hZV
      (forall_mem_pair ⟨hxpV, hxpa, hxpb, hxpp⟩ ⟨hypV, hypa, hypb, hypp⟩)
    intro x _ hxa hxb
    rw [hA, count_pair_v, count_pair_v, count_pair_v, if_neg hxa, if_neg hxb, ind_left, ind_left]
    omega
  have hNqZ : nbrs (rungDel X a b p xp p yp μ) q = {c', d'} := by
    apply nbrs_splice_of (Ne.symm haq) (Ne.symm hbq) hNq (hl q) (hR.rungAdds_count_diag μ q) hZV
      (forall_mem_pair ⟨hcdV.1, hca, hcb, hcdq.1⟩ ⟨hcdV.2, hda, hdb, hcdq.2⟩)
    intro x _ _ _
    rw [hA, count_pair, if_neg (sym2_ne_of (Ne.symm hpq) hqx), if_neg (sym2_ne_of (Ne.symm hpq) hqy)]
    omega
  have hσZ : (rungDel X a b p xp p yp μ).mult s(p, q) = 0 := by
    rw [mult_of_nbrs_eq hNpZ (Ne.symm hpq), count_pair_v, if_neg hqx, if_neg hqy]
  refine ⟨_, isClosureU_y2Move (added' := {s(xp, yp), s(c', d')}) hZV (rungDel_mult X a b p xp p yp μ) hCV hCl
    hCm hQ ?_ ?_ ?_ (by omega) (Or.inl ⟨hσZ, xp, yp, c', d', hNpZ, hNqZ, rfl⟩), (reducesToT_y2Move_iff hQ).mp hRT⟩
  · rw [hA]
    exact forall_mem_pair (Or.inl (Sym2.mem_mk_left _ _)) (Or.inl (Sym2.mem_mk_left _ _))
  · exact forall_mem_pair
      ⟨not_mem_sym2 (Ne.symm hxpp) (Ne.symm hypp), not_mem_sym2 hqx hqy, not_mem_sym2 (Ne.symm hxpa) (Ne.symm hypa),
        not_mem_sym2 (Ne.symm hxpb) (Ne.symm hypb)⟩
      ⟨not_mem_sym2 (Ne.symm hcp) (Ne.symm hdp), not_mem_sym2 (Ne.symm hcdq.1) (Ne.symm hcdq.2),
        not_mem_sym2 (Ne.symm hca) (Ne.symm hda), not_mem_sym2 (Ne.symm hcb) (Ne.symm hdb)⟩
  · intro e _ _ hae _
    rw [count_pair, count_pair, if_neg (fun h => hae (by rw [h]; exact Sym2.mem_mk_left a b))]
    omega

/-- Case (A2): the second joint is the far end of the rail at `a`. -/
theorem capA2 (hT : IsTVineU X p q) (hR : RungCore X a b p q p yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hqy : q ≠ yp) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b p q p yp μ) p q C' ∧ ReducesToT C' := by
  obtain ⟨hl, hNp, hσ, -, hpq, hpV, -, C, c', d', hNq, hCV, hCl, hRT, hCm⟩ := capA_setup hT hR hap haq hbp hbq
  have hpK := hR.xm_mem
  have hypK := hR.yp_mem
  have hypp : yp ≠ p := fun h => hR.not_mem_both hpK (h ▸ hypK)
  obtain ⟨hypV, hypa, hypb⟩ := hR.mem_verts (Or.inr hypK)
  -- the neighbours of `q` are `a` and a further atom `w`
  have hXqa : X.mult s(q, a) = 1 := by
    rw [Sym2.eq_swap, hR.mult_a, if_neg (Ne.symm hbq), if_pos (Or.inr rfl)]
  have hXqb : X.mult s(q, b) = 0 := by
    rw [Sym2.eq_swap, hR.mult_b, if_neg (Ne.symm haq), if_neg]
    rintro (h | h); exacts [hpq h.symm, hqy h]
  have hXqp : X.mult s(q, p) = 0 := by rw [Sym2.eq_swap]; exact hσ
  obtain ⟨w, hw⟩ := pair_eq_of_mem (show a ∈ ({c', d'} : Multiset V) by
    rw [← hNq]; exact (hR.mem_nbrs_of_rail (Ne.symm haq) (Ne.symm hbq)).1 (Or.inr rfl))
  have hNqw : nbrs X q = {a, w} := hNq.trans hw
  rw [sym2_eq_of_pair_eq hw] at hCm
  have hwV := (nbrs_mem_verts hNqw).2
  have hwq := (nbrs_mem_ne hl hNqw).2
  have hwa : w ≠ a := by
    intro h
    have := (mult_of_nbrs_eq hNqw haq).symm.trans hXqa
    rw [count_pair_self, if_pos h.symm] at this
    omega
  have hwb : w ≠ b := (pair_ne_of_count ((mult_of_nbrs_eq hNqw hbq).symm.trans hXqb)).2
  have hwp : w ≠ p := (pair_ne_of_count ((mult_of_nbrs_eq hNqw hpq).symm.trans hXqp)).2
  -- the rung pair is a (Y2) pair of the closure, with externals `w` and `yp`
  have hCa : ∀ x, C.mult s(a, x) = if x = b then 3 else if x = w then 1 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hap) (Ne.symm haq) hCm hR.mult_a x, count_pair, ind_left, ind_left]
    exact rail_closed2 hbp hbq hwp hwq hwb
  have hCb : ∀ x, C.mult s(b, x) = if x = a then 3 else if x = yp then 1 else 0 := by
    intro x
    rw [closure_mult_a (Ne.symm hbp) (Ne.symm hbq) hCm hR.mult_b x, count_pair, ind_right,
      if_neg (sym2_ne_of (Ne.symm hR.ne) (Ne.symm hwb)), add_zero]
    exact rail_closed (Or.inl rfl) hap haq hypp (Ne.symm hqy)
  have hQ := y2Pair_of_reducesToT hR.ne hwa hwb hypa hypb hCa hCb hRT
  -- the joints of the deleted graph
  have hZV := hR.verts_rungDel μ
  have hA := rungAdds_capA p q yp μ
  have hNpZ : nbrs (rungDel X a b p q p yp μ) p = {q, yp} := by
    apply nbrs_splice_of (Ne.symm hap) (Ne.symm hbp) hNp (hl p) (hR.rungAdds_count_diag μ p) hZV
      (forall_mem_pair ⟨(hR.mem_verts (Or.inr hR.xp_mem)).1, Ne.symm haq, Ne.symm hbq, Ne.symm hpq⟩
        ⟨hypV, hypa, hypb, hypp⟩)
    intro x _ hxa hxb
    rw [hA, count_pair_v, count_pair_v, count_pair_v, if_neg hxa, if_neg hxb, ind_left, ind_left]
    omega
  have hNqZ : nbrs (rungDel X a b p q p yp μ) q = {p, w} := by
    apply nbrs_splice_of (Ne.symm haq) (Ne.symm hbq) hNqw (hl q) (hR.rungAdds_count_diag μ q) hZV
      (forall_mem_pair ⟨hpV, Ne.symm hap, Ne.symm hbp, hpq⟩ ⟨hwV, hwa, hwb, hwq⟩)
    intro x _ hxa _
    rw [hA, count_pair_v, count_pair_v, count_pair_v, if_neg hxa, if_neg (sym2_ne_of (Ne.symm hpq) hqy),
      Sym2.eq_swap (a := p) (b := q), ind_left]
    omega
  have hσZ : (rungDel X a b p q p yp μ).mult s(p, q) = 1 := by
    rw [mult_of_nbrs_eq hNpZ (Ne.symm hpq), count_pair_self, if_neg hqy]
  refine ⟨_, isClosureU_y2Move (added' := {s(yp, w)}) hZV (rungDel_mult X a b p q p yp μ) hCV hCl
    hCm hQ ?_ ?_ ?_ (by omega) (Or.inr ⟨hσZ, yp, w, hNpZ, hNqZ, rfl⟩), (reducesToT_y2Move_iff hQ).mp hRT⟩
  · rw [hA]
    exact forall_mem_pair (Or.inl (Sym2.mem_mk_left _ _)) (Or.inl (Sym2.mem_mk_left _ _))
  · exact forall_mem_single
      ⟨not_mem_sym2 (Ne.symm hypp) (Ne.symm hwp), not_mem_sym2 hqy (Ne.symm hwq),
        not_mem_sym2 (Ne.symm hypa) (Ne.symm hwa), not_mem_sym2 (Ne.symm hypb) (Ne.symm hwb)⟩
  · intro e _ _ hae _
    have h1 : ¬ e = s(a, b) := fun h => hae (by rw [h]; exact Sym2.mem_mk_left a b)
    have h2 : ¬ e = s(a, w) := fun h => hae (by rw [h]; exact Sym2.mem_mk_left a w)
    rw [count_pair, if_neg h1, if_neg h2, Multiset.count_singleton, Sym2.eq_swap (a := w) (b := yp)]
    omega

/-- **Case (A)**: the joint `p` carries both rails of the pole `K⁻`. -/
theorem capA (hT : IsTVineU X p q) (hR : RungCore X a b p xp p yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b p xp p yp μ) p q C' ∧ ReducesToT C' := by
  by_cases hqy : q = yp
  · by_cases hqx : q = xp
    · exact (capA_stuck hT hR hap haq hbp hbq hqx hqy).elim
    · rw [rungDel_swapAB]
      subst hqy
      exact capA2 hT hR.swapAB hbp hbq hap haq hqx μ
  · by_cases hqx : q = xp
    · subst hqx
      exact capA2 hT hR hap haq hbp hbq hqy μ
    · exact capA1 hT hR hap haq hbp hbq hqx hqy μ

/-! ## Case (B): the pole `K⁻` is `{p, q}` -/

/-- In case (B), the neighbours of the joint `p = xm` are `a` and the other joint. -/
theorem nbrs_capB {xm' ym : V} (hR : RungCore X a b p xm' ym yp Km Kp) (hl : X.Loopless) (hd : deg X p = 2)
    (hKm : Km ⊆ {p, q}) (hpa : p ≠ a) (hpb : p ≠ b) (hpym : p ≠ ym) : nbrs X p = {a, q} := by
  have hpK := hR.xm_mem
  have ha : a ∈ nbrs X p := (hR.mem_nbrs_of_rail hpa hpb).1 (Or.inl rfl)
  obtain ⟨u, w, huw⟩ := Multiset.card_eq_two.mp (show Multiset.card (nbrs X p) = 2 by rw [card_nbrs]; exact hd)
  rw [huw] at ha
  obtain ⟨w', hw'⟩ := pair_eq_of_mem ha
  have hN : nbrs X p = {a, w'} := huw.trans hw'
  have hXa : X.mult s(p, a) = 1 := by rw [Sym2.eq_swap, hR.mult_a, if_neg hpb, if_pos (Or.inl rfl)]
  have hXb : X.mult s(p, b) = 0 := by
    rw [Sym2.eq_swap, hR.mult_b, if_neg hpa, if_neg]
    rintro (h | h)
    · exact hpym h
    · exact hR.not_mem_both hpK (h ▸ hR.yp_mem)
  have hw'p : w' ≠ p := (nbrs_mem_ne hl hN).2
  have hw'V := (nbrs_mem_verts hN).2
  have hmw : X.mult s(p, w') ≠ 0 := by
    rw [mult_of_nbrs_eq hN hw'p, count_pair_v, if_pos (rfl : w' = w')]; omega
  have hw'a : w' ≠ a := by
    intro h
    rw [mult_of_nbrs_eq hN (Ne.symm hpa), count_pair_self, if_pos h.symm] at hXa
    omega
  have hw'b : w' ≠ b := by intro h; rw [h] at hmw; exact hmw hXb
  rcases hR.mem_poles hw'V hw'a hw'b with hK | hK
  · have := hKm hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hw'p
    · rw [hN, h]
  · exact absurd (hR.noBond p hpK w' hK) hmw

/-- Case (B), for a matching given by the two bonds it adds at `p` and at `q`. -/
theorem capB_core (hT : IsTVineU X p q) (hR : RungCore X a b p xp q yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hKm : Km ⊆ {p, q}) {z z' : V} (μ : Bool)
    (hA : rungAdds p xp q yp μ = {s(p, z), s(q, z')}) (hzz : s(z, z') = s(xp, yp)) (hz : z = xp ∨ z = yp)
    (hz' : z' = xp ∨ z' = yp) :
    ∃ C', IsClosureU (rungDel X a b p xp q yp μ) p q C' ∧ ReducesToT C' := by
  have hl := hT.loopless
  obtain ⟨⟨hpV, hqV, hpq, hdp, hdq, -, -⟩, -, C, ⟨-, hCV, hCl, added, hdata, hCm⟩, hRT⟩ := hT
  have hpK := hR.xm_mem
  have hqK := hR.ym_mem
  have hxpK := hR.xp_mem
  have hypK := hR.yp_mem
  have hxpp : xp ≠ p := fun h => hR.not_mem_both hpK (h ▸ hxpK)
  have hypp : yp ≠ p := fun h => hR.not_mem_both hpK (h ▸ hypK)
  have hxpq : xp ≠ q := fun h => hR.not_mem_both hqK (h ▸ hxpK)
  have hypq : yp ≠ q := fun h => hR.not_mem_both hqK (h ▸ hypK)
  obtain ⟨hxpV, hxpa, hxpb⟩ := hR.mem_verts (Or.inr hxpK)
  obtain ⟨hypV, hypa, hypb⟩ := hR.mem_verts (Or.inr hypK)
  have hzf : ∀ t, (t = xp ∨ t = yp) → t ∈ X.verts ∧ t ≠ p ∧ t ≠ q ∧ t ≠ a ∧ t ≠ b := by
    rintro t (rfl | rfl)
    exacts [⟨hxpV, hxpp, hxpq, hxpa, hxpb⟩, ⟨hypV, hypp, hypq, hypa, hypb⟩]
  obtain ⟨hzV, hzp, hzq, hza, hzb⟩ := hzf z hz
  obtain ⟨hz'V, hz'p, hz'q, hz'a, hz'b⟩ := hzf z' hz'
  have hNp : nbrs X p = {a, q} := nbrs_capB hR hl hdp hKm (Ne.symm hap) (Ne.symm hbp) hpq
  have hNq : nbrs X q = {b, p} :=
    nbrs_capB hR.swapAB hl hdq (by rw [Finset.pair_comm]; exact hKm) (Ne.symm hbq) (Ne.symm haq) (Ne.symm hpq)
  have hσ : X.mult s(p, q) = 1 := by
    rw [mult_of_nbrs_eq hNp (Ne.symm hpq), count_pair_v, if_neg (Ne.symm haq), if_pos rfl]
  -- the closure of `X` joins `a` and `b`
  obtain ⟨x, y, h1, h2, rfl⟩ : ∃ x y : V, nbrs X p = {q, x} ∧ nbrs X q = {p, y} ∧ added = {s(x, y)} := by
    rcases hdata with ⟨h0, -⟩ | ⟨-, x, y, h1, h2, h3⟩
    · omega
    · exact ⟨x, y, h1, h2, h3⟩
  have hxa : x = a := eq_of_pair_eq_pair (h1.symm.trans hNp)
  have hyb : y = b := eq_of_pair_eq_pair (h2.symm.trans hNq)
  subst hxa hyb
  have hCa : ∀ x', C.mult s(x, x') = if x' = y then 3 else if x' = xp then 1 else 0 := by
    intro x'
    rw [closure_mult_a (Ne.symm hap) (Ne.symm haq) hCm hR.mult_a x', Multiset.count_singleton, ind_left]
    exact rail_closed (Or.inl rfl) hbp hbq hxpp hxpq
  have hCb : ∀ x', C.mult s(y, x') = if x' = x then 3 else if x' = yp then 1 else 0 := by
    intro x'
    rw [closure_mult_a (Ne.symm hbp) (Ne.symm hbq) hCm hR.mult_b x', Multiset.count_singleton, ind_right]
    exact rail_closed (Or.inr rfl) hap haq hypp hypq
  have hQ := y2Pair_of_reducesToT hR.ne hxpa hxpb hypa hypb hCa hCb hRT
  -- the joints of the deleted graph
  have hZV := hR.verts_rungDel μ
  have hNpZ : nbrs (rungDel X x y p xp q yp μ) p = {q, z} := by
    apply nbrs_splice_of (Ne.symm hap) (Ne.symm hbp) hNp (hl p) (hR.rungAdds_count_diag μ p) hZV
      (forall_mem_pair ⟨hqV, Ne.symm haq, Ne.symm hbq, Ne.symm hpq⟩ ⟨hzV, hza, hzb, hzp⟩)
    intro x' _ hxa _
    rw [hA, count_pair_v, count_pair_v, count_pair_v, if_neg hxa, ind_left, if_neg (sym2_ne_of hpq (Ne.symm hz'p))]
    omega
  have hNqZ : nbrs (rungDel X x y p xp q yp μ) q = {p, z'} := by
    apply nbrs_splice_of (Ne.symm haq) (Ne.symm hbq) hNq (hl q) (hR.rungAdds_count_diag μ q) hZV
      (forall_mem_pair ⟨hpV, Ne.symm hap, Ne.symm hbp, hpq⟩ ⟨hz'V, hz'a, hz'b, hz'q⟩)
    intro x' _ _ hxb
    rw [hA, count_pair_v, count_pair_v, count_pair_v, if_neg hxb, ind_left,
      if_neg (sym2_ne_of (Ne.symm hpq) (Ne.symm hzq))]
    omega
  have hσZ : (rungDel X x y p xp q yp μ).mult s(p, q) = 1 := by
    rw [mult_of_nbrs_eq hNpZ (Ne.symm hpq), count_pair_self, if_neg (Ne.symm hzq)]
  refine ⟨_, isClosureU_y2Move (added' := {s(z, z')}) hZV (rungDel_mult X x y p xp q yp μ) hCV hCl
    hCm hQ ?_ ?_ ?_ (by omega) (Or.inr ⟨hσZ, z, z', hNpZ, hNqZ, rfl⟩), (reducesToT_y2Move_iff hQ).mp hRT⟩
  · rw [hA]
    exact forall_mem_pair (Or.inl (Sym2.mem_mk_left _ _)) (Or.inr (Sym2.mem_mk_left _ _))
  · exact forall_mem_single
      ⟨not_mem_sym2 (Ne.symm hzp) (Ne.symm hz'p), not_mem_sym2 (Ne.symm hzq) (Ne.symm hz'q),
        not_mem_sym2 (Ne.symm hza) (Ne.symm hz'a), not_mem_sym2 (Ne.symm hzb) (Ne.symm hz'b)⟩
  · intro e _ _ hae _
    have h1 : ¬ e = s(x, y) := fun h => hae (by rw [h]; exact Sym2.mem_mk_left x y)
    rw [Multiset.count_singleton, if_neg h1, Multiset.count_singleton, hzz, zero_add]

/-- **Case (B)**: the pole `K⁻` is `{p, q}`, with rails `a–p` and `b–q`. -/
theorem capB (hT : IsTVineU X p q) (hR : RungCore X a b p xp q yp Km Kp) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hKm : Km ⊆ {p, q}) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b p xp q yp μ) p q C' ∧ ReducesToT C' := by
  cases μ
  · exact capB_core hT hR hap haq hbp hbq hKm false rfl rfl (Or.inl rfl) (Or.inr rfl)
  · refine capB_core hT hR hap haq hbp hbq hKm true ?_ Sym2.eq_swap (Or.inr rfl) (Or.inl rfl)
    show ({s(p, yp), s(xp, q)} : Multiset (Sym2 V)) = _
    rw [Sym2.eq_swap (a := xp) (b := q)]

/-! ## Assembly -/

/-- The cap case with `K⁻ ⊆ {p, q}` and `xm = p`. -/
theorem capKm_p {ym : V} (hT : IsTVineU X p q) (hR : RungCore X a b p xp ym yp Km Kp) (hap : a ≠ p)
    (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hKm : Km ⊆ {p, q}) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b p xp ym yp μ) p q C' ∧ ReducesToT C' := by
  have hym : ym = p ∨ ym = q := by have := hKm hR.ym_mem; simpa using this
  rcases hym with rfl | rfl
  · exact capA hT hR hap haq hbp hbq μ
  · exact capB hT hR hap haq hbp hbq hKm μ

/-- The cap case with `K⁻ ⊆ {p, q}`. -/
theorem capKm {xm ym : V} (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp) (hap : a ≠ p)
    (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hKm : Km ⊆ {p, q}) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b xm xp ym yp μ) p q C' ∧ ReducesToT C' := by
  have hxm : xm = p ∨ xm = q := by have := hKm hR.xm_mem; simpa using this
  rcases hxm with rfl | rfl
  · exact capKm_p hT hR hap haq hbp hbq hKm μ
  · obtain ⟨C', hC', hRT⟩ := capKm_p hT.swap hR haq hap hbq hbp (by rw [Finset.pair_comm]; exact hKm) μ
    exact ⟨C', hC'.swap, hRT⟩

/-- The closure part of a cap deletion. -/
theorem cap_closure {xm ym : V} (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp) (hap : a ≠ p)
    (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hcap : IsCapAt p q Km Kp) (μ : Bool) :
    ∃ C', IsClosureU (rungDel X a b xm xp ym yp μ) p q C' ∧ ReducesToT C' := by
  rcases hcap with h | h
  · exact capKm hT hR hap haq hbp hbq h μ
  · rw [rungDel_swapPoles]
    exact capKm hT hR.swapPoles hap haq hbp hbq h μ

end Cap

/-- **Cap deletion** (N3 §2.1 (ii), second bullet; N2 Lemma 1.9(1) without the non-cap hypothesis): deleting a
cap rung of a T-vine (given by rung data, rung atoms not joints), with either matching, gives a T-vine with the
same joints. -/
theorem isTVineU_rungDel_cap {X : UMultigraph V} {p q a b xm xp ym yp : V} {Km Kp : Finset V}
    (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hcap : IsCapAt p q Km Kp) (μ : Bool) :
    IsTVineU (rungDel X a b xm xp ym yp μ) p q := by
  obtain ⟨hB', hm2'⟩ := rungDel_block_of_tvine hT hR hap haq hbp hbq μ
  obtain ⟨C', hC', hRT'⟩ := cap_closure hT hR hap haq hbp hbq hcap μ
  exact ⟨hB', hm2', C', hC', hRT'⟩

/-- **Rung deletion in a T-vine**: any rung (given by rung data, rung atoms not joints) of a T-vine can be deleted,
with either matching, giving a T-vine with the same joints. -/
theorem isTVineU_rungDel_any {X : UMultigraph V} {p q a b xm xp ym yp : V} {Km Kp : Finset V}
    (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (μ : Bool) :
    IsTVineU (rungDel X a b xm xp ym yp μ) p q := by
  by_cases hcap : IsCapAt p q Km Kp
  · exact isTVineU_rungDel_cap hT hR hap haq hbp hbq hcap μ
  · exact isTVineU_rungDel_of_noncap hT hR hap haq hbp hbq hcap μ

end WaveTurbulence.TVine.Core

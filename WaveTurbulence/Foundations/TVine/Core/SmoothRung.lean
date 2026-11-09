/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Smooth

/-!
# Smoothing a joint commutes with rung deletion (N2 Lemma 1.9 proof; REF-M4 §2.3 "cl(B/[μ]R) = cl(B)/[μ]R")

For rung data `R` and a degree-2 atom `j ∉ R`:
* `smooth_rungDel_free`: `j` is not a rail end; the rails stay;
* `smooth_rungDel_rail`: `j = xm` (with neighbours `a, w`); after smoothing, `a`'s rail goes to `w`;
in both cases `(G/[μ]R)` smoothed at `j` is `(G smoothed at j)/[μ]R`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

section

variable {G : UMultigraph V} {a b xm xp ym yp j : V} {Km Kp : Finset V}

theorem RungCore.union_erase (hR : RungCore G a b xm xp ym yp Km Kp) {j n n' : V} (hn : n ∈ G.verts)
    (hn' : n' ∈ G.verts) (hjP : j ∉ Kp) :
    Km.erase j ∪ Kp = ((smooth G j n n').verts.erase a).erase b := by
  rw [smooth_verts hn hn']
  ext x
  have hu := Finset.ext_iff.mp hR.union x
  simp only [Finset.mem_union, Finset.mem_erase] at hu ⊢
  constructor
  · rintro (⟨hxj, hx⟩ | hx)
    · exact ⟨(hu.mp (Or.inl hx)).1, (hu.mp (Or.inl hx)).2.1, hxj, (hu.mp (Or.inl hx)).2.2⟩
    · refine ⟨(hu.mp (Or.inr hx)).1, (hu.mp (Or.inr hx)).2.1, ?_, (hu.mp (Or.inr hx)).2.2⟩
      rintro rfl; exact hjP hx
  · rintro ⟨hxb, hxa, hxj, hx⟩
    rcases hu.mpr ⟨hxb, hxa, hx⟩ with h | h
    · exact Or.inl ⟨hxj, h⟩
    · exact Or.inr h

/-- Smoothing a free atom of `Km` (not a rail end). -/
theorem smooth_rungDel_free {n n' : V} (hR : RungCore G a b xm xp ym yp Km Kp) (hj : j ∈ Km)
    (hjm : j ≠ xm) (hjm' : j ≠ ym) (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'}) :
    n ∈ Km ∧ n' ∈ Km ∧ RungCore (smooth G j n n') a b xm xp ym yp (Km.erase j) Kp ∧
      ∀ μ : Bool, nbrs (rungDel G a b xm xp ym yp μ) j = {n, n'} ∧
        smooth (rungDel G a b xm xp ym yp μ) j n n' = rungDel (smooth G j n n') a b xm xp ym yp μ := by
  have hjP : j ∉ Kp := fun h => hR.not_mem_both hj h
  have hjxp : j ≠ xp := fun h => hjP (h ▸ hR.xp_mem)
  have hjyp : j ≠ yp := fun h => hjP (h ▸ hR.yp_mem)
  obtain ⟨hja, hjb⟩ := hR.ne_of_mem (Or.inl hj)
  have hnj : n ≠ j ∧ n' ≠ j := by
    have := not_mem_nbrs_of_loop hl
    rw [hnb] at this
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at this
    exact ⟨Ne.symm this.1, Ne.symm this.2⟩
  have hnV := nbrs_mem_verts hnb
  have hna : n ≠ a ∧ n' ≠ a := by
    have h1 := mult_of_nbrs_eq hnb (Ne.symm hja)
    rw [Sym2.eq_swap, hR.mult_a, if_neg hjb, if_neg (by rintro (h | h); exacts [hjm h, hjxp h])] at h1
    have h0 := Multiset.count_eq_zero.mp h1.symm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at h0
    exact ⟨Ne.symm h0.1, Ne.symm h0.2⟩
  have hnb' : n ≠ b ∧ n' ≠ b := by
    have h1 := mult_of_nbrs_eq hnb (Ne.symm hjb)
    rw [Sym2.eq_swap, hR.mult_b, if_neg hja, if_neg (by rintro (h | h); exacts [hjm' h, hjyp h])] at h1
    have h0 := Multiset.count_eq_zero.mp h1.symm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at h0
    exact ⟨Ne.symm h0.1, Ne.symm h0.2⟩
  have hnK : n ∈ Km := hR.mem_Km_of_mult hj (by
    rw [mult_of_nbrs_eq hnb hnj.1, count_pair_self]; omega) hna.1 hnb'.1
  have hn'K : n' ∈ Km := hR.mem_Km_of_mult hj (by
    rw [mult_of_nbrs_eq hnb hnj.2, Multiset.pair_comm, count_pair_self]; omega) hna.2 hnb'.2
  have hsa : s(a, n) ≠ s(n, n') ∨ True := Or.inr trivial
  have hC1 : RungCore (smooth G j n n') a b xm xp ym yp (Km.erase j) Kp := by
    refine ⟨hR.ne, fun x => ?_, fun x => ?_, ?_, hR.union_erase hnV.1 hnV.2 hjP, ?_, ?_, hR.xp_mem, ?_,
      hR.yp_mem⟩
    · rw [smooth_mult_at G (Ne.symm hja), hR.mult_a]
      have e : s(a, x) ≠ s(n, n') := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hna.1 h1.symm, hna.2 h1.symm]
      by_cases hx : x = j
      · rw [if_pos hx, hx]; simp [hjb, hjm, hjxp]
      · rw [if_neg hx, if_neg e, add_zero]
    · rw [smooth_mult_at G (Ne.symm hjb), hR.mult_b]
      have e : s(b, x) ≠ s(n, n') := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hnb'.1 h1.symm, hnb'.2 h1.symm]
      by_cases hx : x = j
      · rw [if_pos hx, hx]; simp [hja, hjm', hjyp]
      · rw [if_neg hx, if_neg e, add_zero]
    · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hR.disj
    · intro u hu w hw
      have hu' := Finset.mem_of_mem_erase hu
      have huj := Finset.ne_of_mem_erase hu
      have hwj : w ≠ j := fun h => hjP (h ▸ hw)
      rw [smooth_mult_at G huj, if_neg hwj, hR.noBond u hu' w hw, zero_add, if_neg]
      intro h; rcases Sym2.eq_iff.mp h with ⟨_, h1⟩ | ⟨_, h1⟩
      · exact hR.not_mem_both hn'K (h1 ▸ hw)
      · exact hR.not_mem_both hnK (h1 ▸ hw)
    · exact Finset.mem_erase.mpr ⟨Ne.symm hjm, hR.xm_mem⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hjm', hR.ym_mem⟩
  refine ⟨hnK, hn'K, hC1, fun μ => ⟨?_, ?_⟩⟩
  · apply nbrs_eq_of_mult
    · rw [hR.rungDel_mult_inner hja hjb hjm hjxp hjm' hjyp, hl]
    · intro x hx
      rw [hR.verts_rungDel]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simp [hna.1, hnb'.1, hnV.1], hnj.1⟩
      · exact ⟨by simp [hna.2, hnb'.2, hnV.2], hnj.2⟩
    · intro x hx
      rw [hR.rungDel_mult_inner hja hjb hjm hjxp hjm' hjyp, mult_of_nbrs_eq hnb hx]
  · have hB1 : ∀ f ∈ ({s(n, n')} : Multiset (Sym2 V)), a ∉ f ∧ b ∉ f := by
      intro f hf
      rw [Multiset.mem_singleton] at hf
      subst hf
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hna.1, Ne.symm hna.2⟩, ⟨Ne.symm hnb'.1, Ne.symm hnb'.2⟩⟩
    have hB2 : ∀ f ∈ rungAdds xm xp ym yp μ, j ∉ f ∧ j ∉ f := fun f hf =>
      ⟨rungAdds_not_mem hjm hjxp hjm' hjyp μ f hf, rungAdds_not_mem hjm hjxp hjm' hjyp μ f hf⟩
    apply ext
    · rw [smooth_verts, hR.verts_rungDel, hC1.verts_rungDel, smooth_verts hnV.1 hnV.2]
      · ext x; simp only [Finset.mem_erase]; tauto
      · rw [hR.verts_rungDel]; simp [hna.1, hnb'.1, hnV.1]
      · rw [hR.verts_rungDel]; simp [hna.2, hnb'.2, hnV.2]
    · intro e
      simp only [smooth, rungDel]
      rw [splice_splice_mult _ _ _ hB1, splice_splice_mult _ _ _ hB2]
      by_cases h : j ∈ e ∨ a ∈ e ∨ b ∈ e
      · rw [if_pos (by tauto), if_pos (by tauto)]
      · rw [if_neg (by tauto), if_neg (by tauto)]; ring

/-- Smoothing the rail end `j = xm` (neighbours `a`, `w`). -/
theorem smooth_rungDel_rail {w : V} (hR : RungCore G a b j xp ym yp Km Kp) (hjm' : j ≠ ym)
    (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {a, w}) :
    w ∈ Km ∧ w ≠ j ∧ RungCore (smooth G j a w) a b w xp ym yp (Km.erase j) Kp ∧
      ∀ μ : Bool, nbrs (rungDel G a b j xp ym yp μ) j = {w, if μ then yp else xp} ∧
        smooth (rungDel G a b j xp ym yp μ) j w (if μ then yp else xp) =
          rungDel (smooth G j a w) a b w xp ym yp μ := by
  have hj := hR.xm_mem
  have hjP : j ∉ Kp := fun h => hR.not_mem_both hj h
  have hjxp : j ≠ xp := fun h => hjP (h ▸ hR.xp_mem)
  have hjyp : j ≠ yp := fun h => hjP (h ▸ hR.yp_mem)
  obtain ⟨hja, hjb⟩ := hR.ne_of_mem (Or.inl hj)
  have hwj : w ≠ j := by
    have := not_mem_nbrs_of_loop hl
    rw [hnb] at this
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at this
    exact Ne.symm this.2
  have hnV := nbrs_mem_verts hnb
  have hwa : w ≠ a := by
    intro h
    have h1 := mult_of_nbrs_eq hnb (Ne.symm hja)
    rw [Sym2.eq_swap, hR.mult_a, if_neg hjb, if_pos (Or.inl rfl), h, count_pair_self, if_pos rfl] at h1
    omega
  have hwb : w ≠ b := by
    intro h
    have h1 := mult_of_nbrs_eq hnb (Ne.symm hjb)
    rw [Sym2.eq_swap, hR.mult_b, if_neg hja, if_neg (by rintro (h | h); exacts [hjm' h, hjyp h]), ← h,
      count_pair_of_ne hwa, if_pos rfl] at h1
    omega
  have hwK : w ∈ Km := hR.mem_Km_of_mult hj (by
    rw [mult_of_nbrs_eq hnb hwj, count_pair_of_ne hwa, if_pos rfl]; omega) hwa hwb
  have hwxp : w ≠ xp := fun h => hR.not_mem_both hwK (h ▸ hR.xp_mem)
  have hC1 : RungCore (smooth G j a w) a b w xp ym yp (Km.erase j) Kp := by
    refine ⟨hR.ne, fun x => ?_, fun x => ?_, ?_, hR.union_erase hnV.1 hnV.2 hjP, ?_, ?_, hR.xp_mem, ?_,
      hR.yp_mem⟩
    · rw [smooth_mult_at G (Ne.symm hja), hR.mult_a]
      have hiff : (s(a, x) = s(a, w)) ↔ x = w := Sym2.congr_right
      by_cases hx : x = j
      · rw [if_pos hx, hx]; simp [hjb, Ne.symm hwj, hjxp]
      · rw [if_neg hx]
        by_cases hxb : x = b
        · rw [if_neg (mt hiff.mp (fun h => hwb (h.symm.trans hxb))), hxb]; simp
        · by_cases hxw : x = w
          · rw [if_pos (hiff.mpr hxw), hxw]; simp [hwb, hwj, hwxp]
          · rw [if_neg (mt hiff.mp hxw)]
            by_cases hxx : x = xp
            · rw [hxx]; simp [hwxp.symm, hjxp.symm, Ne.symm (fun h : xp = b => (hR.ne_of_mem (Or.inr hR.xp_mem)).2 h)]
            · simp [hxb, hx, hxw, hxx]
    · rw [smooth_mult_at G (Ne.symm hjb), hR.mult_b]
      have e : s(b, x) ≠ s(a, w) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hR.ne h1.symm, hwb h1.symm]
      by_cases hx : x = j
      · rw [if_pos hx, hx]; simp [hja, hjm', hjyp]
      · rw [if_neg hx, if_neg e, add_zero]
    · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hR.disj
    · intro u hu w' hw'
      have hu' := Finset.mem_of_mem_erase hu
      have huj := Finset.ne_of_mem_erase hu
      have hwj' : w' ≠ j := fun h => hjP (h ▸ hw')
      rw [smooth_mult_at G huj, if_neg hwj', hR.noBond u hu' w' hw', zero_add, if_neg]
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h1⟩
      · exact (hR.ne_of_mem (Or.inl hu')).1 h1
      · exact (hR.ne_of_mem (Or.inr hw')).1 h1
    · exact Finset.mem_erase.mpr ⟨hwj, hwK⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hjm', hR.ym_mem⟩
  refine ⟨hwK, hwj, hC1, fun μ => ?_⟩
  set z := if μ then yp else xp with hz
  have hzK : z ∈ Kp := by cases μ <;> simp [hz, hR.xp_mem, hR.yp_mem]
  obtain ⟨hza, hzb⟩ := hR.ne_of_mem (Or.inr hzK)
  have hzj : z ≠ j := fun h => hjP (h ▸ hzK)
  have hzw : z ≠ w := fun h => hR.not_mem_both hwK (h ▸ hzK)
  have hzV := (hR.mem_verts (Or.inr hzK)).1
  have hcnt := rungAdds_count_xm hjm' hjxp hjyp μ
  refine ⟨?_, ?_⟩
  · apply nbrs_eq_of_mult
    · rw [rungDel, splice_mult_at _ _ hja hjb, if_neg (by tauto), hl, hcnt, if_neg (Ne.symm hzj)]
    · intro x hx
      rw [hR.verts_rungDel]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simp [hwa, hwb, hnV.2], hwj⟩
      · exact ⟨by simp [hza, hzb, hzV], hzj⟩
    · intro x hx
      rw [rungDel, splice_mult_at _ _ hja hjb, hcnt]
      by_cases hxab : x = a ∨ x = b
      · rw [if_pos hxab]
        rcases hxab with rfl | rfl
        · rw [count_pair_of_ne (Ne.symm hwa), if_neg (Ne.symm hza)]
        · rw [count_pair_of_ne (Ne.symm hwb), if_neg (Ne.symm hzb)]
      · rw [if_neg hxab, mult_of_nbrs_eq hnb hx, count_pair_of_ne (fun h => hxab (Or.inl h))]
        by_cases hxw : x = w
        · subst hxw; rw [if_pos rfl, count_pair_self, if_neg (Ne.symm hzw)]
        · rw [if_neg hxw, zero_add, count_pair_of_ne hxw]
  · have hB1 : ∀ f ∈ ({s(w, z)} : Multiset (Sym2 V)), a ∉ f ∧ b ∉ f := by
      intro f hf
      rw [Multiset.mem_singleton] at hf
      subst hf
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hwa, Ne.symm hza⟩, ⟨Ne.symm hwb, Ne.symm hzb⟩⟩
    have hB2 : ∀ f ∈ rungAdds w xp ym yp μ, j ∉ f ∧ j ∉ f := fun f hf =>
      ⟨rungAdds_not_mem (Ne.symm hwj) hjxp hjm' hjyp μ f hf,
        rungAdds_not_mem (Ne.symm hwj) hjxp hjm' hjyp μ f hf⟩
    apply ext
    · rw [smooth_verts, hR.verts_rungDel, hC1.verts_rungDel, smooth_verts hnV.1 hnV.2]
      · ext x; simp only [Finset.mem_erase]; tauto
      · rw [hR.verts_rungDel]; simp [hwa, hwb, hnV.2]
      · rw [hR.verts_rungDel]; simp [hza, hzb, hzV]
    · intro e
      simp only [smooth, rungDel]
      rw [splice_splice_mult _ _ _ hB1, splice_splice_mult _ _ _ hB2]
      by_cases h : j ∈ e ∨ a ∈ e ∨ b ∈ e
      · rw [if_pos (by tauto), if_pos (by tauto)]
      · rw [if_neg (by tauto), if_neg (by tauto)]
        have hje : j ∉ e := fun h' => h (Or.inl h')
        have hae : a ∉ e := fun h' => h (Or.inr (Or.inl h'))
        have e1 : e ≠ s(a, w) := fun h' => hae (h' ▸ Sym2.mem_mk_left a w)
        have e2 : e ≠ s(j, yp) := fun h' => hje (h' ▸ Sym2.mem_mk_left j yp)
        have e3 : e ≠ s(j, xp) := fun h' => hje (h' ▸ Sym2.mem_mk_left j xp)
        cases μ
        · simp only [hz, rungAdds, Bool.false_eq_true, if_false, count_pair, Multiset.count_singleton, e1, e3,
            ↓reduceIte]
          ring
        · simp only [hz, rungAdds, if_true, count_pair, Multiset.count_singleton, e1, e2, ↓reduceIte]
          ring

end

end WaveTurbulence.TVine.Core

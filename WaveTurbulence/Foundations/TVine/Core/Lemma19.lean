/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.SmoothRung

/-!
# N2 Lemma 1.9(1): deleting a deletable rung keeps a T-vine a T-vine (path-wise)

`isTVineU_rungDel`: if `(G, j₁, j₂)` is a T-vine and `R = {a, b}` a deletable rung, then `G/[μ]R` is a T-vine, for
either matching `μ`. Proof (N2 Lemma 1.9, REF-M4 §2.3): the block and multiplicity conditions directly; the closure
of `G/[μ]R` is `cl(G)/[μ]R'` (`R'` the rung with smoothed rails, `smooth_rungDel_step` twice), and Lemma 1.5
(path-wise, Lemmas 5′/5″) transfers `→* T`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

section Step

variable {G : UMultigraph V} {a b xm xp ym yp j n n' : V} {Km Kp : Finset V}

/-- The general joint step inside `Km`. -/
private theorem step_Km (hR : RungCore G a b xm xp ym yp Km Kp) (hjK : j ∈ Km)
    (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'}) (hab : ¬ (a ∈ nbrs G j ∧ b ∈ nbrs G j)) :
    ∃ xm' xp' ym' yp' : V, RungCore (smooth G j n n') a b xm' xp' ym' yp' (Km.erase j) Kp ∧
      ∀ μ : Bool, ∃ m m' : V, nbrs (rungDel G a b xm xp ym yp μ) j = {m, m'} ∧
        smooth (rungDel G a b xm xp ym yp μ) j m m' = rungDel (smooth G j n n') a b xm' xp' ym' yp' μ := by
  obtain ⟨hja, hjb⟩ := hR.ne_of_mem (Or.inl hjK)
  have ha_of : j = xm → a ∈ nbrs G j := fun h => by
    apply Multiset.count_pos.mp
    rw [count_nbrs, if_pos hR.a_verts, if_neg hja, Sym2.eq_swap, hR.mult_a, if_neg hjb,
      if_pos (Or.inl h)]; omega
  have hb_of : j = ym → b ∈ nbrs G j := fun h => by
    apply Multiset.count_pos.mp
    rw [count_nbrs, if_pos hR.b_verts, if_neg hjb, Sym2.eq_swap, hR.mult_b, if_neg hja,
      if_pos (Or.inl h)]; omega
  by_cases hjm : j = xm
  · subst hjm
    have hjm' : j ≠ ym := fun h => hab ⟨ha_of rfl, hb_of h⟩
    obtain ⟨w, hw⟩ := pair_eq_of_mem (by rw [← hnb]; exact ha_of rfl)
    have hs : smooth G j n n' = smooth G j a w := by unfold smooth; rw [sym2_eq_of_pair_eq hw]
    obtain ⟨-, -, hC1, hμ⟩ := smooth_rungDel_rail hR hjm' hl (hnb.trans hw)
    refine ⟨w, xp, ym, yp, by rw [hs]; exact hC1, fun μ => ⟨w, if μ then yp else xp, (hμ μ).1, ?_⟩⟩
    rw [hs]; exact (hμ μ).2
  by_cases hjm' : j = ym
  · subst hjm'
    obtain ⟨w, hw⟩ := pair_eq_of_mem (by rw [← hnb]; exact hb_of rfl)
    have hs : smooth G j n n' = smooth G j b w := by unfold smooth; rw [sym2_eq_of_pair_eq hw]
    obtain ⟨-, -, hC1, hμ⟩ := smooth_rungDel_rail hR.swapAB hjm hl (hnb.trans hw)
    refine ⟨xm, xp, w, yp, by rw [hs]; exact hC1.swapAB, fun μ => ⟨w, if μ then xp else yp, ?_, ?_⟩⟩
    · rw [rungDel_swapAB]; exact (hμ μ).1
    · rw [rungDel_swapAB, hs, rungDel_swapAB (smooth G j b w)]; exact (hμ μ).2
  obtain ⟨-, -, hC1, hμ⟩ := smooth_rungDel_free hR hjK hjm hjm' hl hnb
  exact ⟨xm, xp, ym, yp, hC1, fun μ => ⟨n, n', hμ μ⟩⟩

/-- **The joint step**: smoothing a degree-2 atom `j ∉ R` that is not adjacent to both `a` and `b`. -/
theorem smooth_rungDel_step (hR : RungCore G a b xm xp ym yp Km Kp) (hjV : j ∈ G.verts) (hja : j ≠ a)
    (hjb : j ≠ b) (hl : G.mult s(j, j) = 0) (hnb : nbrs G j = {n, n'})
    (hab : ¬ (a ∈ nbrs G j ∧ b ∈ nbrs G j)) :
    ∃ xm' xp' ym' yp' : V, RungCore (smooth G j n n') a b xm' xp' ym' yp' (Km.erase j) (Kp.erase j) ∧
      ∀ μ : Bool, ∃ m m' : V, nbrs (rungDel G a b xm xp ym yp μ) j = {m, m'} ∧
        smooth (rungDel G a b xm xp ym yp μ) j m m' = rungDel (smooth G j n n') a b xm' xp' ym' yp' μ := by
  rcases hR.mem_poles hjV hja hjb with hjK | hjK
  · have hP : Kp.erase j = Kp := Finset.erase_eq_of_notMem fun h => hR.not_mem_both hjK h
    rw [hP]
    exact step_Km hR hjK hl hnb hab
  · have hP : Km.erase j = Km := Finset.erase_eq_of_notMem fun h => hR.not_mem_both h hjK
    obtain ⟨xm', xp', ym', yp', hC1, hμ⟩ := step_Km hR.swapPoles hjK hl hnb hab
    refine ⟨xp', xm', yp', ym', by rw [hP]; exact hC1.swapPoles, fun μ => ?_⟩
    obtain ⟨m, m', h1, h2⟩ := hμ μ
    refine ⟨m, m', ?_, ?_⟩
    · rw [rungDel_swapPoles]; exact h1
    · rw [rungDel_swapPoles, h2, rungDel_swapPoles]

end Step

/-! ## The deleted graph: degrees, connectivity, multiplicities -/

section Del

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem sum_ind_sym2 {S : Finset V} {v x y : V} (hxy : x ≠ y) (hx : x ∈ S) (hy : y ∈ S) :
    ∑ w ∈ S, (if s(v, w) = s(x, y) then 1 else 0) = (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
  by_cases hvx : v = x
  · subst hvx
    have : ∀ w, (s(v, w) = s(v, y)) ↔ w = y := fun w => Sym2.congr_right
    simp only [this, Finset.sum_ite_eq', hy, if_true, if_neg hxy]
  · by_cases hvy : v = y
    · subst hvy
      have : ∀ w, (s(v, w) = s(x, v)) ↔ w = x := fun w => by rw [Sym2.eq_swap (a := x), Sym2.congr_right]
      simp only [this, Finset.sum_ite_eq', hx, if_true, if_neg hvx]
    · have : ∀ w, ¬ (s(v, w) = s(x, y)) := fun w h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        exacts [hvx h1, hvy h1]
      simp [this, hvx, hvy]

/-- Deleting a rung does not change the degrees of the other atoms. -/
theorem RungCore.deg_rungDel (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) {v : V} (hva : v ≠ a)
    (hvb : v ≠ b) : deg (rungDel G a b xm xp ym yp μ) v = deg G v := by
  have hxmV := hR.mem_verts (Or.inl hR.xm_mem)
  have hxpV := hR.mem_verts (Or.inr hR.xp_mem)
  have hymV := hR.mem_verts (Or.inl hR.ym_mem)
  have hypV := hR.mem_verts (Or.inr hR.yp_mem)
  set S := (G.verts.erase a).erase b with hS
  have hmem : ∀ {x}, x ∈ G.verts → x ≠ a → x ≠ b → x ∈ S := fun h1 h2 h3 => by simp [hS, h1, h2, h3]
  have hm : ∀ w ∈ S, (rungDel G a b xm xp ym yp μ).mult s(v, w) =
      G.mult s(v, w) + (rungAdds xm xp ym yp μ).count s(v, w) := by
    intro w hw
    simp only [hS, Finset.mem_erase] at hw
    rw [rungDel, splice_mult_at _ _ hva hvb, if_neg (by tauto)]
  have hloop : (rungAdds xm xp ym yp μ).count s(v, v) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro h
    cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton] at h <;>
      rcases h with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
      | exact hR.not_mem_both hR.xm_mem (h1.symm.trans h2 ▸ hR.yp_mem)
      | exact hR.not_mem_both hR.ym_mem (h2.symm.trans h1 ▸ hR.xp_mem)
      | exact hR.not_mem_both hR.xm_mem (h1.symm.trans h2 ▸ hR.xp_mem)
      | exact hR.not_mem_both hR.ym_mem (h1.symm.trans h2 ▸ hR.yp_mem)
      | exact hR.not_mem_both hR.xm_mem (h2.symm.trans h1 ▸ hR.yp_mem)
      | exact hR.not_mem_both hR.ym_mem (h1.symm.trans h2 ▸ hR.xp_mem)
      | exact hR.not_mem_both hR.xm_mem (h2.symm.trans h1 ▸ hR.xp_mem)
      | exact hR.not_mem_both hR.ym_mem (h2.symm.trans h1 ▸ hR.yp_mem)
  have hvv : (rungDel G a b xm xp ym yp μ).mult s(v, v) = G.mult s(v, v) := by
    rw [rungDel, splice_mult_at _ _ hva hvb, if_neg (by tauto), hloop, add_zero]
  -- the added bonds at `v` count the rails at `v`
  have hA : ∑ w ∈ S, (rungAdds xm xp ym yp μ).count s(v, w) = G.mult s(v, a) + G.mult s(v, b) := by
    have ha := hR.mult_a v
    have hb := hR.mult_b v
    rw [Sym2.eq_swap] at ha hb
    rw [ha, hb, if_neg hvb, if_neg hva]
    have hxx := hR.xm_ne_xp
    have hyy := hR.ym_ne_yp
    have hxyp : xm ≠ yp := fun h => hR.not_mem_both hR.xm_mem (h ▸ hR.yp_mem)
    have hxpym : xp ≠ ym := fun h => hR.not_mem_both hR.ym_mem (h ▸ hR.xp_mem)
    cases μ
    · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair, Finset.sum_add_distrib]
      rw [sum_ind_sym2 hxx (hmem hxmV.1 hxmV.2.1 hxmV.2.2) (hmem hxpV.1 hxpV.2.1 hxpV.2.2),
        sum_ind_sym2 hyy (hmem hymV.1 hymV.2.1 hymV.2.2) (hmem hypV.1 hypV.2.1 hypV.2.2)]
      by_cases h1 : v = xm <;> by_cases h2 : v = xp <;> by_cases h3 : v = ym <;> by_cases h4 : v = yp <;>
        simp_all
    · simp only [rungAdds, if_true, count_pair, Finset.sum_add_distrib]
      rw [sum_ind_sym2 hxyp (hmem hxmV.1 hxmV.2.1 hxmV.2.2) (hmem hypV.1 hypV.2.1 hypV.2.2),
        sum_ind_sym2 hxpym (hmem hxpV.1 hxpV.2.1 hxpV.2.2) (hmem hymV.1 hymV.2.1 hymV.2.2)]
      by_cases h1 : v = xm <;> by_cases h2 : v = xp <;> by_cases h3 : v = ym <;> by_cases h4 : v = yp <;>
        simp_all
  rw [deg, deg, hR.verts_rungDel, ← hS, Finset.sum_congr rfl hm, Finset.sum_add_distrib, hA, hvv]
  have hb' : b ∈ G.verts.erase a := Finset.mem_erase.mpr ⟨hR.ne.symm, hR.b_verts⟩
  rw [← Finset.add_sum_erase _ _ hR.a_verts, ← Finset.add_sum_erase _ _ hb', ← hS]
  ring

/-- Bonds between the poles of `G/[μ]R` are the two added bonds; at most `2`. -/
theorem RungCore.rungDel_mult_le (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) {u w : V}
    (hu : u ∈ Km) (hw : w ∈ Kp) : (rungDel G a b xm xp ym yp μ).mult s(u, w) ≤ 2 := by
  rw [hR.rungDel_mult_cross hu hw]
  have := Multiset.count_le_card s(u, w) (rungAdds xm xp ym yp μ)
  have hc : Multiset.card (rungAdds xm xp ym yp μ) = 2 := by cases μ <;> rfl
  omega

/-- Inside a pole, deletion changes no bond. -/
theorem RungCore.rungDel_mult_same (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) {u w : V}
    (h : (u ∈ Km ∧ w ∈ Km) ∨ (u ∈ Kp ∧ w ∈ Kp)) :
    (rungDel G a b xm xp ym yp μ).mult s(u, w) = G.mult s(u, w) := by
  have hu : u ∈ Km ∨ u ∈ Kp := by tauto
  obtain ⟨hua, hub⟩ := hR.ne_of_mem hu
  have hw : w ∈ Km ∨ w ∈ Kp := by tauto
  obtain ⟨hwa, hwb⟩ := hR.ne_of_mem hw
  rw [rungDel, splice_mult_at _ _ hua hub, if_neg (by tauto)]
  have : (rungAdds xm xp ym yp μ).count s(u, w) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hf
    have hcross : ∀ f ∈ rungAdds xm xp ym yp μ, ∃ x ∈ Km, ∃ y ∈ Kp, f = s(x, y) := by
      intro f hf
      cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
        Multiset.mem_cons, Multiset.mem_singleton] at hf <;> rcases hf with rfl | rfl
      · exact ⟨xm, hR.xm_mem, xp, hR.xp_mem, rfl⟩
      · exact ⟨ym, hR.ym_mem, yp, hR.yp_mem, rfl⟩
      · exact ⟨xm, hR.xm_mem, yp, hR.yp_mem, rfl⟩
      · exact ⟨ym, hR.ym_mem, xp, hR.xp_mem, Sym2.eq_swap⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hcross _ hf
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
      | exact hR.not_mem_both h1 hx | exact hR.not_mem_both h2 hy
      | exact hR.not_mem_both hx h1 | exact hR.not_mem_both hy h2
      | exact hR.not_mem_both h2 hx | exact hR.not_mem_both h1 hy
      | exact hR.not_mem_both hx h2 | exact hR.not_mem_both hy h1
  rw [this, add_zero]

end Del

end WaveTurbulence.TVine.Core

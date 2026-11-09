/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiGap

/-!
# N2 Lemma 1.14(d): gap freeness transfers along rung deletion

`phiGap_holds : PhiGapStatement`. Proof (N2 Lemma 1.14(d), contrapositive, combinatorial reading of the gap via
`GapCutAt`, cf. N2 Lemma 1.13): a gap cut `X` of `U` in `G` (normalised so that `k₁ ∈ X`) has as its only crossing
bonds the two `U°`-bonds at `k₁`; the rung lies on one side. If it lies outside, `X` itself is a gap cut of `Φ(U)` in
`G/[μ]R` (a rail crosses only at `k₁`, and then the added bond at `k₁` crosses instead); if inside, `X ∖ R` is.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- Double indicator sums over crossing pairs. -/
theorem dsum_ind_sym2 {T Y : Finset V} {x y : V} (hxy : x ≠ y) (hxT : x ∈ T) (hyT : y ∈ T) :
    ∑ u ∈ Y, ∑ w ∈ T \ Y, (if s(u, w) = s(x, y) then 1 else 0) =
      (if x ∈ Y ∧ y ∉ Y then 1 else 0) + (if y ∈ Y ∧ x ∉ Y then 1 else 0) := by
  have hrow : ∀ u, ∑ w ∈ T \ Y, (if s(u, w) = s(x, y) then 1 else 0) =
      (if u = x ∧ y ∉ Y then 1 else 0) + (if u = y ∧ x ∉ Y then 1 else 0) := by
    intro u
    by_cases hux : u = x
    · subst hux
      have : ∀ w, (s(u, w) = s(u, y)) ↔ w = y := fun w => Sym2.congr_right
      simp only [this, Finset.sum_ite_eq', Finset.mem_sdiff, hyT, true_and, hxy, false_and, if_false,
        add_zero]
    · by_cases huy : u = y
      · subst huy
        have : ∀ w, (s(u, w) = s(x, u)) ↔ w = x := fun w => by rw [Sym2.eq_swap (a := x), Sym2.congr_right]
        simp only [this, Finset.sum_ite_eq', Finset.mem_sdiff, hxT, true_and, hux, false_and, if_false,
          zero_add]
      · have : ∀ w, ¬ (s(u, w) = s(x, y)) := fun w h => by
          rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
          exacts [hux h1, huy h1]
        simp [this, hux, huy]
  rw [Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_add_distrib]
  have e : ∀ (z : V) (P : Prop) [Decidable P], ∑ u ∈ Y, (if u = z ∧ P then 1 else 0) =
      if z ∈ Y ∧ P then 1 else 0 := by
    intro z P _
    by_cases hP : P
    · simp only [hP, and_true]; rw [Finset.sum_ite_eq']
    · simp [hP]
  rw [e x (y ∉ Y), e y (x ∉ Y)]

section Del

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {μ : Bool}

/-- The added bonds crossing a set avoiding the rung, when the rail ends in it lie in one pole. -/
theorem adds_cross_count (hR : RungCore G a b xm xp ym yp Km Kp) {Y : Finset V} (hYV : Y ⊆ G.verts)
    (haY : a ∉ Y) (hbY : b ∉ Y) (hone : ¬ ((xm ∈ Y ∨ ym ∈ Y) ∧ (xp ∈ Y ∨ yp ∈ Y))) :
    ∑ u ∈ Y, ∑ w ∈ (rungDel G a b xm xp ym yp μ).verts \ Y, (rungAdds xm xp ym yp μ).count s(u, w) =
      (if xm ∈ Y then 1 else 0) + (if xp ∈ Y then 1 else 0) + (if ym ∈ Y then 1 else 0) +
        (if yp ∈ Y then 1 else 0) := by
  have hDV : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hR.verts_rungDel μ
  have hT : ∀ x, (x ∈ Km ∨ x ∈ Kp) → x ∈ (rungDel G a b xm xp ym yp μ).verts := by
    intro x hx; rw [hDV]
    obtain ⟨hxV, hxa, hxb⟩ := hR.mem_verts hx
    simp [hxV, hxa, hxb]
  have hxm := hT xm (Or.inl hR.xm_mem)
  have hxp := hT xp (Or.inr hR.xp_mem)
  have hym := hT ym (Or.inl hR.ym_mem)
  have hyp := hT yp (Or.inr hR.yp_mem)
  have hne : ∀ {x y}, x ∈ Km → y ∈ Kp → x ≠ y := fun hx hy h => hR.not_mem_both hx (h ▸ hy)
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair, Finset.sum_add_distrib]
    rw [dsum_ind_sym2 (hne hR.xm_mem hR.xp_mem) hxm hxp, dsum_ind_sym2 (hne hR.ym_mem hR.yp_mem) hym hyp]
    by_cases h1 : xm ∈ Y <;> by_cases h2 : xp ∈ Y <;> by_cases h3 : ym ∈ Y <;> by_cases h4 : yp ∈ Y <;>
      simp_all
  · simp only [rungAdds, if_true, count_pair, Finset.sum_add_distrib]
    rw [dsum_ind_sym2 (hne hR.xm_mem hR.yp_mem) hxm hyp, dsum_ind_sym2 (Ne.symm (hne hR.ym_mem hR.xp_mem)) hxp hym]
    by_cases h1 : xm ∈ Y <;> by_cases h2 : xp ∈ Y <;> by_cases h3 : ym ∈ Y <;> by_cases h4 : yp ∈ Y <;>
      simp_all

/-- For an all-in sub-object, a bond of `U°` at a rung atom is a bond of `G`. -/
theorem core_mult_rung {U : SubObj V} {x v : V} (hxS : x ∈ U.atoms) (hvS : v ∈ U.atoms)
    (hx1 : U.k₁ ≠ x) (hx2 : U.k₂ ≠ x) : (U.core G).mult s(v, x) = G.mult s(v, x) := by
  have hne : s(v, x) ≠ s(U.k₁, U.k₂) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
    exacts [hx2 h2.symm, hx1 h2.symm]
  unfold SubObj.core SubObj.edges
  split
  · show (if s(v, x) = s(U.k₁, U.k₂) then _ else _) = _
    rw [if_neg hne, induce_mult_of_mem G hvS hxS]
  · exact induce_mult_of_mem G hvS hxS

/-- For an all-in sub-object, `Φ(U)°` has the same degrees as `U°` at the remaining atoms. -/
theorem deg_core_phi_allIn (hR : RungCore G a b xm xp ym yp Km Kp) {U : SubObj V} (hU : IsSubObjU G U)
    (haS : a ∈ U.atoms) (hbS : b ∈ U.atoms)
    (hrails : xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b)
    (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b) {v : V} (hvS : v ∈ U.atoms) (hva : v ≠ a) (hvb : v ≠ b) :
    deg ((U.phi a b).core (rungDel G a b xm xp ym yp μ)) v = deg (U.core G) v := by
  set S := (U.atoms.erase a).erase b with hS
  have hSV : ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).verts = S := by
    rw [SubObj.core_verts]; rfl
  have hmem : ∀ {x}, x ∈ U.atoms → x ≠ a → x ≠ b → x ∈ S := fun h1 h2 h3 => by simp [hS, h1, h2, h3]
  have hm : ∀ w ∈ S, ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(v, w) =
      (U.core G).mult s(v, w) + (rungAdds xm xp ym yp μ).count s(v, w) := by
    intro w hw
    simp only [hS, Finset.mem_erase] at hw
    exact core_rungDel_allIn hU hrails
      (by intro h; rcases Sym2.mem_iff.mp h with h | h; exacts [hva h.symm, hw.2.1 h.symm])
      (by intro h; rcases Sym2.mem_iff.mp h with h | h; exacts [hvb h.symm, hw.1 h.symm])
  have hvv : ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(v, v) = (U.core G).mult s(v, v) := by
    rw [hm v (hmem hvS hva hvb), hR.rungAdds_count_diag, add_zero]
  have hA : ∑ w ∈ S, (rungAdds xm xp ym yp μ).count s(v, w) =
      (U.core G).mult s(v, a) + (U.core G).mult s(v, b) := by
    rw [core_mult_rung haS hvS h1a h2a, core_mult_rung hbS hvS h1b h2b]
    have ha := hR.mult_a v
    have hb := hR.mult_b v
    rw [Sym2.eq_swap] at ha hb
    rw [ha, hb, if_neg hvb, if_neg hva]
    obtain ⟨hxm, hxp, hym, hyp⟩ := hrails
    have hK : ∀ x, (x ∈ Km ∨ x ∈ Kp) → x ∈ U.atoms → x ∈ S := fun x hx hxS =>
      hmem hxS (hR.ne_of_mem hx).1 (hR.ne_of_mem hx).2
    have hxx := hR.xm_ne_xp
    have hyy := hR.ym_ne_yp
    have hxyp : xm ≠ yp := fun h => hR.not_mem_both hR.xm_mem (h ▸ hR.yp_mem)
    have hxpym : xp ≠ ym := fun h => hR.not_mem_both hR.ym_mem (h ▸ hR.xp_mem)
    cases μ
    · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair, Finset.sum_add_distrib]
      rw [sum_ind_sym2 hxx (hK xm (Or.inl hR.xm_mem) hxm) (hK xp (Or.inr hR.xp_mem) hxp),
        sum_ind_sym2 hyy (hK ym (Or.inl hR.ym_mem) hym) (hK yp (Or.inr hR.yp_mem) hyp)]
      by_cases h1 : v = xm <;> by_cases h2 : v = xp <;> by_cases h3 : v = ym <;> by_cases h4 : v = yp <;>
        simp_all
    · simp only [rungAdds, if_true, count_pair, Finset.sum_add_distrib]
      rw [sum_ind_sym2 hxyp (hK xm (Or.inl hR.xm_mem) hxm) (hK yp (Or.inr hR.yp_mem) hyp),
        sum_ind_sym2 hxpym (hK xp (Or.inr hR.xp_mem) hxp) (hK ym (Or.inl hR.ym_mem) hym)]
      by_cases h1 : v = xm <;> by_cases h2 : v = xp <;> by_cases h3 : v = ym <;> by_cases h4 : v = yp <;>
        simp_all
  unfold deg
  rw [hSV, Finset.sum_congr rfl hm, Finset.sum_add_distrib, hA, hvv, SubObj.core_verts]
  have hb' : b ∈ U.atoms.erase a := Finset.mem_erase.mpr ⟨fun h => hR.ne h.symm, hbS⟩
  rw [← Finset.add_sum_erase _ _ haS, ← Finset.add_sum_erase _ _ hb', ← hS]
  ring

end Del

/-- A gap cut from a side `X'` containing `k` whose `Φ`-bonds at `k` all leave it. -/
theorem gapCutAt_of_side {H : UMultigraph V} {W : SubObj V} {k : V} (hdeg : deg (W.core H) k = 2)
    (hl : (W.core H).mult s(k, k) = 0) {X' : Finset V} (hX'V : X' ⊆ H.verts) (hcut : cut H X' = 2)
    (hk : k ∈ X') (hout : ∀ w, (W.core H).mult s(k, w) ≠ 0 → w ∉ X') : GapCutAt H W k := by
  have hc : Multiset.card (nbrs (W.core H) k) = 2 := by rw [card_nbrs]; exact hdeg
  obtain ⟨m₁, m₂, hM⟩ := Multiset.card_eq_two.mp hc
  have hMk := nbrs_ne_of_loop hl hM
  have hm₁ : (W.core H).mult s(k, m₁) ≠ 0 := by
    rw [mult_of_nbrs_eq hM hMk.1, count_pair_self]; omega
  have hm₂ : (W.core H).mult s(k, m₂) ≠ 0 := by
    rw [mult_of_nbrs_eq hM hMk.2, Multiset.pair_comm, count_pair_self]; omega
  exact ⟨X', hX'V, hcut, m₁, m₂, hM, ⟨fun _ => hout m₁ hm₁, fun _ => hk⟩, ⟨fun _ => hout m₂ hm₂, fun _ => hk⟩⟩

/-- The normal form of a gap cut of a sub-object: `k₁` inside, its two `U°`-neighbours outside, and these carry
the only crossing bonds. -/
theorem gapCut_normal {G : UMultigraph V} {U : SubObj V} (hl : G.Loopless) (hU : IsSubObjU G U)
    (hgap : GapCutAt G U U.k₁) :
    ∃ X₀ : Finset V, ∃ n₁ n₂ : V, X₀ ⊆ G.verts ∧ cut G X₀ = 2 ∧ U.k₁ ∈ X₀ ∧ n₁ ∈ G.verts \ X₀ ∧
      n₂ ∈ G.verts \ X₀ ∧ (∀ w, (U.core G).mult s(U.k₁, w) ≠ 0 → w = n₁ ∨ w = n₂) ∧
      (∀ u ∈ X₀, ∀ w ∈ G.verts \ X₀, G.mult s(u, w) ≠ 0 → u = U.k₁ ∧ (w = n₁ ∨ w = n₂)) := by
  obtain ⟨X, hXV, hcut, n₁, n₂, hN, hc₁, hc₂⟩ := hgap
  have hcoreL : ∀ v, (U.core G).mult s(v, v) = 0 := fun v => Nat.le_zero.mp (hl v ▸ core_mult_le G U _)
  have hnk := nbrs_ne_of_loop (hcoreL U.k₁) hN
  have hnS := nbrs_mem_verts hN
  rw [SubObj.core_verts] at hnS
  have hn₁V := hU.atoms_subset hnS.1
  have hn₂V := hU.atoms_subset hnS.2
  have hkV := hU.atoms_subset hU.k₁_mem
  have hc₁G : 1 ≤ G.mult s(U.k₁, n₁) := by
    have h := mult_of_nbrs_eq hN hnk.1
    rw [count_pair_self] at h
    have := core_mult_le G U s(U.k₁, n₁); omega
  have hc₂G : 1 ≤ G.mult s(U.k₁, n₂) := by
    have h := mult_of_nbrs_eq hN hnk.2
    rw [Multiset.pair_comm, count_pair_self] at h
    have := core_mult_le G U s(U.k₁, n₂); omega
  have hc₁₂ : n₁ = n₂ → 2 ≤ G.mult s(U.k₁, n₁) := by
    intro h
    have h' := mult_of_nbrs_eq hN hnk.1
    rw [count_pair_self, if_pos h] at h'
    have := core_mult_le G U s(U.k₁, n₁); omega
  have hNmem : ∀ w, (U.core G).mult s(U.k₁, w) ≠ 0 → w = n₁ ∨ w = n₂ := by
    intro w hw
    have hwk : w ≠ U.k₁ := by rintro rfl; exact hw (hcoreL _)
    rw [mult_of_nbrs_eq hN hwk] at hw
    exact pair_count_pos (Nat.pos_of_ne_zero hw)
  obtain ⟨X₀, hX₀V, hcut₀, hkX₀, hn₁X₀, hn₂X₀⟩ :
      ∃ X₀ ⊆ G.verts, cut G X₀ = 2 ∧ U.k₁ ∈ X₀ ∧ n₁ ∉ X₀ ∧ n₂ ∉ X₀ := by
    by_cases hkX : U.k₁ ∈ X
    · exact ⟨X, hXV, hcut, hkX, hc₁.mp hkX, hc₂.mp hkX⟩
    · refine ⟨G.verts \ X, Finset.sdiff_subset, by rw [cut_compl G hXV]; exact hcut,
        Finset.mem_sdiff.mpr ⟨hkV, hkX⟩, ?_, ?_⟩
      · intro h; exact (Finset.mem_sdiff.mp h).2 (by by_contra h'; exact hkX (hc₁.mpr h'))
      · intro h; exact (Finset.mem_sdiff.mp h).2 (by by_contra h'; exact hkX (hc₂.mpr h'))
  exact ⟨X₀, n₁, n₂, hX₀V, hcut₀, hkX₀, Finset.mem_sdiff.mpr ⟨hn₁V, hn₁X₀⟩, Finset.mem_sdiff.mpr ⟨hn₂V, hn₂X₀⟩,
    hNmem, gapCut_crossing hcut₀ hkX₀ (Finset.mem_sdiff.mpr ⟨hn₁V, hn₁X₀⟩)
      (Finset.mem_sdiff.mpr ⟨hn₂V, hn₂X₀⟩) hc₁G hc₂G hc₁₂⟩

section Bonds

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {μ : Bool} {U : SubObj V}

/-- The bonds of `Φ(U)°` at `k₁`: bonds of `U°`, or (all-in) added bonds. -/
theorem phi_bond_at_k (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U)
    (hcls : (a ∈ U.inner ∧ b ∈ U.inner ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms)) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (w : V)
    (hw : ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(U.k₁, w) ≠ 0) :
    w ≠ a ∧ w ≠ b ∧ ((U.core G).mult s(U.k₁, w) ≠ 0 ∨
      (a ∈ U.atoms ∧ (rungAdds xm xp ym yp μ).count s(U.k₁, w) ≠ 0)) := by
  have hwS := Finset.mem_sym2_iff.mp (core_mult_supp _ _ hw) w (Sym2.mem_mk_right _ w)
  simp only [SubObj.phi, Finset.mem_erase] at hwS
  refine ⟨hwS.2.1, hwS.1, ?_⟩
  have hae : a ∉ s(U.k₁, w) := by
    intro h; rcases Sym2.mem_iff.mp h with h | h; exacts [h1a h.symm, hwS.2.1 h.symm]
  have hbe : b ∉ s(U.k₁, w) := by
    intro h; rcases Sym2.mem_iff.mp h with h | h; exacts [h1b h.symm, hwS.1 h.symm]
  rcases hcls with ⟨ha, hb, hrails⟩ | ⟨ha, hb⟩
  · rw [core_rungDel_allIn hU hrails hae hbe] at hw
    by_cases h0 : (U.core G).mult s(U.k₁, w) = 0
    · rw [h0, zero_add] at hw; exact Or.inr ⟨U.inner_subset ha, hw⟩
    · exact Or.inl h0
  · obtain ⟨h1, h2⟩ := core_rungDel_allOut (μ := μ) hR hU ha hb
    rw [h1, h2] at hw; exact Or.inl hw

/-- An added bond at `k₁` (all-in) makes `k₁` a rail end with a rung atom among its `U°`-neighbours. -/
theorem phi_added_at_k (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U) (haS : a ∈ U.atoms)
    (hbS : b ∈ U.atoms) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b)
    {n₁ n₂ : V} (hNmem : ∀ w, (U.core G).mult s(U.k₁, w) ≠ 0 → w = n₁ ∨ w = n₂) {w : V}
    (hw : (rungAdds xm xp ym yp μ).count s(U.k₁, w) ≠ 0) :
    (a = n₁ ∨ a = n₂ ∨ b = n₁ ∨ b = n₂) ∧ (w = xm ∨ w = xp ∨ w = ym ∨ w = yp) ∧ w ≠ U.k₁ := by
  obtain ⟨x, y, hxy, hx, hy⟩ := rungAdds_mem (Multiset.count_ne_zero.mp hw)
  have hxK : x ∈ Km := by rcases hx with rfl | rfl; exacts [hR.xm_mem, hR.ym_mem]
  have hyK : y ∈ Kp := by rcases hy with rfl | rfl; exacts [hR.xp_mem, hR.yp_mem]
  have hxy' : x ≠ y := fun h => hR.not_mem_both hxK (h ▸ hyK)
  have hkrail : U.k₁ = xm ∨ U.k₁ = xp ∨ U.k₁ = ym ∨ U.k₁ = yp := by
    rcases Sym2.eq_iff.mp hxy with ⟨h, -⟩ | ⟨h, -⟩
    · rcases hx with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (Or.inr (Or.inl (h.trans h')))
    · rcases hy with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (Or.inr (h.trans h')))
  have hA : (U.k₁ = xm ∨ U.k₁ = xp) → a = n₁ ∨ a = n₂ := by
    intro h
    apply hNmem a
    rw [core_mult_rung haS hU.k₁_mem h1a h2a, Sym2.eq_swap, hR.mult_a, if_neg h1b, if_pos h]; omega
  have hB : (U.k₁ = ym ∨ U.k₁ = yp) → b = n₁ ∨ b = n₂ := by
    intro h
    apply hNmem b
    rw [core_mult_rung hbS hU.k₁_mem h1b h2b, Sym2.eq_swap, hR.mult_b, if_neg h1a, if_pos h]; omega
  refine ⟨?_, ?_, ?_⟩
  · rcases hkrail with h | h | h | h
    · rcases hA (Or.inl h) with h' | h' <;> simp [h']
    · rcases hA (Or.inr h) with h' | h' <;> simp [h']
    · rcases hB (Or.inl h) with h' | h' <;> simp [h']
    · rcases hB (Or.inr h) with h' | h' <;> simp [h']
  · rcases Sym2.eq_iff.mp hxy with ⟨-, h⟩ | ⟨-, h⟩
    · rcases hy with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (Or.inr (h.trans h')))
    · rcases hx with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (Or.inr (Or.inl (h.trans h')))
  · rcases Sym2.eq_iff.mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact Ne.symm hxy'
    · rw [h1, h2]; exact hxy'

/-- The case of the rung inside the normalised gap cut. -/
theorem phiGap_side_in (hR' : IsRungAt G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U)
    (hcls : (a ∈ U.inner ∧ b ∈ U.inner ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms)) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b)
    {X₀ : Finset V} {n₁ n₂ : V} (hX₀V : X₀ ⊆ G.verts) (hcut₀ : cut G X₀ = 2) (hkX₀ : U.k₁ ∈ X₀)
    (hn₁ : n₁ ∈ G.verts \ X₀) (hn₂ : n₂ ∈ G.verts \ X₀)
    (hNmem : ∀ w, (U.core G).mult s(U.k₁, w) ≠ 0 → w = n₁ ∨ w = n₂)
    (hcross : ∀ u ∈ X₀, ∀ w ∈ G.verts \ X₀, G.mult s(u, w) ≠ 0 → u = U.k₁ ∧ (w = n₁ ∨ w = n₂))
    (haX : a ∈ X₀) (hbX : b ∈ X₀) :
    ∃ X' ⊆ (rungDel G a b xm xp ym yp μ).verts, cut (rungDel G a b xm xp ym yp μ) X' = 2 ∧ U.k₁ ∈ X' ∧
      ∀ w, ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(U.k₁, w) ≠ 0 → w ∉ X' := by
  have hRc := hR'.toCore
  have hDV : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hRc.verts_rungDel μ
  set Y := G.verts \ X₀ with hY
  have hYV : Y ⊆ G.verts := Finset.sdiff_subset
  have haY : a ∉ Y := fun h => (Finset.mem_sdiff.mp h).2 haX
  have hbY : b ∉ Y := fun h => (Finset.mem_sdiff.mp h).2 hbX
  have hnoR : ∀ x, (x = xm ∨ x = xp ∨ x = ym ∨ x = yp) → x ∉ Y := by
    intro x hx hxY
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1a (hcross a haX x hxY (by rw [hR'.a_xm]; omega)).1.symm
    · exact h1a (hcross a haX x hxY (by rw [hR'.a_xp]; omega)).1.symm
    · exact h1b (hcross b hbX x hxY (by rw [hR'.b_ym]; omega)).1.symm
    · exact h1b (hcross b hbX x hxY (by rw [hR'.b_yp]; omega)).1.symm
  have hcY := cut_rungDel_avoid (μ := μ) hRc hYV haY hbY
  rw [adds_cross_count hRc hYV haY hbY (by
    rintro ⟨h | h, -⟩
    · exact hnoR xm (Or.inl rfl) h
    · exact hnoR ym (Or.inr (Or.inr (Or.inl rfl))) h)] at hcY
  rw [if_neg (hnoR xm (Or.inl rfl)), if_neg (hnoR xp (Or.inr (Or.inl rfl))),
    if_neg (hnoR ym (Or.inr (Or.inr (Or.inl rfl)))), if_neg (hnoR yp (Or.inr (Or.inr (Or.inr rfl)))),
    cut_compl G hX₀V] at hcY
  have hYD : Y ⊆ (rungDel G a b xm xp ym yp μ).verts := by
    rw [hDV]; intro x hx
    simp only [Finset.mem_erase]
    exact ⟨fun h => hbY (h ▸ hx), fun h => haY (h ▸ hx), hYV hx⟩
  refine ⟨(rungDel G a b xm xp ym yp μ).verts \ Y, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · rw [cut_compl _ hYD]; omega
  · rw [hDV]
    simp only [Finset.mem_sdiff, Finset.mem_erase, hY, not_and, not_not]
    exact ⟨⟨Ne.symm (Ne.symm h1b), Ne.symm (Ne.symm h1a), hX₀V hkX₀⟩, fun _ => hkX₀⟩
  · intro w hw hwX
    obtain ⟨-, -, hw'⟩ := phi_bond_at_k hRc hU hcls h1a h1b w hw
    have hwY : w ∉ Y := (Finset.mem_sdiff.mp hwX).2
    rcases hw' with h | ⟨haS, h⟩
    · rcases hNmem w h with rfl | rfl
      · exact hwY hn₁
      · exact hwY hn₂
    · have hbS : b ∈ U.atoms := by
        rcases hcls with ⟨-, hb, -⟩ | ⟨ha, -⟩
        · exact U.inner_subset hb
        · exact absurd haS ha
      obtain ⟨habn, -, -⟩ := phi_added_at_k hRc hU haS hbS h1a h1b h2a h2b hNmem h
      have h₁ := (Finset.mem_sdiff.mp hn₁).2
      have h₂ := (Finset.mem_sdiff.mp hn₂).2
      rcases habn with h' | h' | h' | h'
      · exact h₁ (h' ▸ haX)
      · exact h₂ (h' ▸ haX)
      · exact h₁ (h' ▸ hbX)
      · exact h₂ (h' ▸ hbX)

/-- The case of the rung outside the normalised gap cut. -/
theorem phiGap_side_out (hR' : IsRungAt G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U)
    (hcls : (a ∈ U.inner ∧ b ∈ U.inner ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms)) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b)
    {X₀ : Finset V} {n₁ n₂ : V} (hX₀V : X₀ ⊆ G.verts) (hcut₀ : cut G X₀ = 2) (hkX₀ : U.k₁ ∈ X₀)
    (hn₁ : n₁ ∈ G.verts \ X₀) (hn₂ : n₂ ∈ G.verts \ X₀)
    (hNmem : ∀ w, (U.core G).mult s(U.k₁, w) ≠ 0 → w = n₁ ∨ w = n₂)
    (hcross : ∀ u ∈ X₀, ∀ w ∈ G.verts \ X₀, G.mult s(u, w) ≠ 0 → u = U.k₁ ∧ (w = n₁ ∨ w = n₂))
    (haX : a ∉ X₀) (hbX : b ∉ X₀) :
    ∃ X' ⊆ (rungDel G a b xm xp ym yp μ).verts, cut (rungDel G a b xm xp ym yp μ) X' = 2 ∧ U.k₁ ∈ X' ∧
      ∀ w, ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(U.k₁, w) ≠ 0 → w ∉ X' := by
  have hRc := hR'.toCore
  have hDV : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hRc.verts_rungDel μ
  have haV : a ∈ G.verts \ X₀ := Finset.mem_sdiff.mpr ⟨hR'.a_mem, haX⟩
  have hbV : b ∈ G.verts \ X₀ := Finset.mem_sdiff.mpr ⟨hR'.b_mem, hbX⟩
  have hrailk : ∀ x, (x = xm ∨ x = xp ∨ x = ym ∨ x = yp) → x ∈ X₀ → x = U.k₁ := by
    intro x hx hxX
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hcross x hxX a haV (by rw [Sym2.eq_swap, hR'.a_xm]; omega)).1
    · exact (hcross x hxX a haV (by rw [Sym2.eq_swap, hR'.a_xp]; omega)).1
    · exact (hcross x hxX b hbV (by rw [Sym2.eq_swap, hR'.b_ym]; omega)).1
    · exact (hcross x hxX b hbV (by rw [Sym2.eq_swap, hR'.b_yp]; omega)).1
  have hone : ¬ ((xm ∈ X₀ ∨ ym ∈ X₀) ∧ (xp ∈ X₀ ∨ yp ∈ X₀)) := by
    rintro ⟨h1, h2⟩
    have hK1 : U.k₁ ∈ Km := by
      rcases h1 with h | h
      · rw [← hrailk xm (Or.inl rfl) h]; exact hRc.xm_mem
      · rw [← hrailk ym (Or.inr (Or.inr (Or.inl rfl))) h]; exact hRc.ym_mem
    have hK2 : U.k₁ ∈ Kp := by
      rcases h2 with h | h
      · rw [← hrailk xp (Or.inr (Or.inl rfl)) h]; exact hRc.xp_mem
      · rw [← hrailk yp (Or.inr (Or.inr (Or.inr rfl))) h]; exact hRc.yp_mem
    exact hRc.not_mem_both hK1 hK2
  have hcX := cut_rungDel_avoid (μ := μ) hRc hX₀V haX hbX
  rw [adds_cross_count hRc hX₀V haX hbX hone] at hcX
  refine ⟨X₀, ?_, by omega, hkX₀, ?_⟩
  · rw [hDV]; intro x hx
    simp only [Finset.mem_erase]
    exact ⟨fun h => hbX (h ▸ hx), fun h => haX (h ▸ hx), hX₀V hx⟩
  · intro w hw hwX
    obtain ⟨-, -, hw'⟩ := phi_bond_at_k hRc hU hcls h1a h1b w hw
    rcases hw' with h | ⟨haS, h⟩
    · rcases hNmem w h with rfl | rfl
      · exact (Finset.mem_sdiff.mp hn₁).2 hwX
      · exact (Finset.mem_sdiff.mp hn₂).2 hwX
    · have hbS : b ∈ U.atoms := by
        rcases hcls with ⟨-, hb, -⟩ | ⟨ha, -⟩
        · exact U.inner_subset hb
        · exact absurd haS ha
      obtain ⟨-, hwr, hwk⟩ := phi_added_at_k hRc hU haS hbS h1a h1b h2a h2b hNmem h
      exact hwk (hrailk w hwr hwX)

end Bonds

/-- **N2 Lemma 1.14(d)** (gap freeness transfers back along rung deletion). -/
theorem phiGap_holds : PhiGapStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp U μ hB hl hR hU h1a h1b h2a h2b hfree hgap
  apply hfree
  have hR' := hR.1
  have hRc := hR'.toCore
  have hcls := phiAllInOut_holds G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hR hU h1a h1b h2a h2b
  obtain ⟨X₀, n₁, n₂, hX₀V, hcut₀, hkX₀, hn₁, hn₂, hNmem, hcross⟩ := gapCut_normal hl hU hgap
  have hDl := hRc.loopless_rungDel hl μ
  have hΦl : ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(U.k₁, U.k₁) = 0 :=
    Nat.le_zero.mp (hDl U.k₁ ▸ core_mult_le _ _ _)
  have hdeg : deg ((U.phi a b).core (rungDel G a b xm xp ym yp μ)) U.k₁ = 2 := by
    rcases hcls with ⟨ha, hb, hrails⟩ | ⟨ha, hb⟩
    · rw [deg_core_phi_allIn hRc hU (U.inner_subset ha) (U.inner_subset hb) hrails h1a h1b h2a h2b
        hU.k₁_mem h1a h1b]
      exact hU.2.2.2.2.2.1
    · obtain ⟨h1, h2⟩ := core_rungDel_allOut (μ := μ) hRc hU ha hb
      rw [h1, h2]; exact hU.2.2.2.2.2.1
  have hab : a ∈ X₀ ↔ b ∈ X₀ := by
    have hab2 : G.mult s(a, b) ≠ 0 := by rw [hR'.mult_ab]; omega
    constructor
    · intro ha; by_contra hb
      exact h1a (hcross a ha b (Finset.mem_sdiff.mpr ⟨hR'.b_mem, hb⟩) hab2).1.symm
    · intro hb; by_contra ha
      exact h1b (hcross b hb a (Finset.mem_sdiff.mpr ⟨hR'.a_mem, ha⟩) (by rw [Sym2.eq_swap]; exact hab2)).1.symm
  have hside : ∃ X' ⊆ (rungDel G a b xm xp ym yp μ).verts, cut (rungDel G a b xm xp ym yp μ) X' = 2 ∧
      U.k₁ ∈ X' ∧ ∀ w, ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult s(U.k₁, w) ≠ 0 → w ∉ X' := by
    by_cases haX : a ∈ X₀
    · exact phiGap_side_in hR' hU hcls h1a h1b h2a h2b hX₀V hcut₀ hkX₀ hn₁ hn₂ hNmem hcross haX (hab.mp haX)
    · exact phiGap_side_out hR' hU hcls h1a h1b h2a h2b hX₀V hcut₀ hkX₀ hn₁ hn₂ hNmem hcross haX
        (fun h => haX (hab.mpr h))
  obtain ⟨X', hX'V, hcut', hkX', hout⟩ := hside
  exact gapCutAt_of_side hdeg hΦl hX'V hcut' hkX' hout

end WaveTurbulence.TVine.Core

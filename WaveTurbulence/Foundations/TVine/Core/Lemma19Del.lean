/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma19

/-!
# N2 Lemma 1.9(1), assembled

`isTVineU_rungDel`: a T-vine stays a T-vine when a deletable rung is deleted, for either matching.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## T-vines are loopless -/

theorem IsTVineU.loopless {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) : G.Loopless := by
  obtain ⟨⟨hj₁V, hj₂V, hj, -⟩, -, C, ⟨-, -, hCl, added, hdata, hm⟩, -⟩ := hT
  intro v
  by_cases hv : v = j₁ ∨ v = j₂
  · rcases hdata with ⟨-, a, b, c, d, h1, h2, rfl⟩ | ⟨-, x, y, h1, h2, -⟩
    · rcases hv with rfl | rfl
      · have h := loop_of_nbrs_eq h1 hj₁V
        by_contra hne
        have hc : 2 ≤ ({a, b} : Multiset V).count v := by omega
        have ha : a = v ∧ b = v := by
          rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hc
          split_ifs at hc with h3 h4 <;> first | omega | exact ⟨h4.symm, h3.symm⟩ | exact ⟨h3.symm, h4.symm⟩
        have := hCl v
        rw [hm, if_pos (Or.inl (Sym2.mem_mk_left v v)), zero_add, ha.1, ha.2, count_pair_self] at this
        omega
      · have h := loop_of_nbrs_eq h2 hj₂V
        by_contra hne
        have hc : 2 ≤ ({c, d} : Multiset V).count v := by omega
        have hc' : c = v ∧ d = v := by
          rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hc
          split_ifs at hc with h3 h4 <;> first | omega | exact ⟨h4.symm, h3.symm⟩ | exact ⟨h3.symm, h4.symm⟩
        have := hCl v
        rw [hm, if_pos (Or.inr (Sym2.mem_mk_left v v)), zero_add, hc'.1, hc'.2, count_pair,
          if_pos rfl] at this
        omega
    · rcases hv with rfl | rfl
      · have h := loop_of_nbrs_eq h1 hj₁V
        rw [count_pair_of_ne hj] at h
        split_ifs at h <;> omega
      · have h := loop_of_nbrs_eq h2 hj₂V
        rw [count_pair_of_ne (Ne.symm hj)] at h
        split_ifs at h <;> omega
  · have := hCl v
    rw [hm, if_neg] at this
    · omega
    · rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h <;> exact hv (by tauto)

/-! ## Closed sets in a connected pole -/

theorem eq_of_closed {G : UMultigraph V} {K S : Finset V} {a b : V} (hK : ConnOn G K)
    (hKab : ∀ x ∈ K, x ≠ a ∧ x ≠ b) (hS : S ⊆ K) (hne : S.Nonempty)
    (hcl : ∀ u ∈ S, ∀ w, G.mult s(u, w) ≠ 0 → w ∈ S ∨ w = a ∨ w = b) : S = K := by
  apply Finset.Subset.antisymm hS
  intro w hw
  obtain ⟨s₀, hs₀⟩ := hne
  suffices H : ∀ v, Relation.ReflTransGen (AdjIn G K) s₀ v → v ∈ S from H w (hK s₀ (hS hs₀) w hw)
  intro v hv
  induction hv with
  | refl => exact hs₀
  | tail _ hstep ih =>
    obtain ⟨-, hv, hm⟩ := hstep
    rcases hcl _ ih _ hm with h | h | h
    · exact h
    · exact absurd h (hKab _ hv).1
    · exact absurd h (hKab _ hv).2

theorem nbrs_closed {G : UMultigraph V} {v x y : V} (h : nbrs G v = {x, y}) (hl : G.mult s(v, v) = 0) (w : V)
    (hw : G.mult s(v, w) ≠ 0) : w = x ∨ w = y := by
  have hwv : w ≠ v := by rintro rfl; exact hw hl
  rw [mult_of_nbrs_eq h hwv] at hw
  exact pair_count_pos (Nat.pos_of_ne_zero hw)

/-- In a block, a joint adjacent to both atoms of a non-cap 2-cut rung would be a cap. -/
theorem IsRungAt.not_both_of_joint {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : IsRungAt G a b xm xp ym yp Km Kp) (hncap : ¬ IsCapAt j₁ j₂ Km Kp) {j : V} (hj : j = j₁ ∨ j = j₂)
    (hjV : j ∈ G.verts) (hja : j ≠ a) (hjb : j ≠ b) (hl : G.mult s(j, j) = 0) {n n' : V}
    (hnb : nbrs G j = {n, n'}) : ¬ (a ∈ nbrs G j ∧ b ∈ nbrs G j) := by
  rintro ⟨ha, hb⟩
  rw [hnb] at ha hb
  obtain ⟨w, hw⟩ := pair_eq_of_mem ha
  rw [hw] at hb hnb
  have hwb : w = b := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb
    rcases hb with h | h
    · exact absurd h.symm hR.ne
    · exact h.symm
  rw [hwb] at hnb
  have hC := hR.toCore
  have hcl : ∀ u ∈ ({j} : Finset V), ∀ w, G.mult s(u, w) ≠ 0 → w ∈ ({j} : Finset V) ∨ w = a ∨ w = b := by
    intro u hu w hw
    rw [Finset.mem_singleton] at hu; subst hu
    exact Or.inr (nbrs_closed hnb hl w hw)
  have hjS : ({j} : Finset V) ⊆ {j₁, j₂} := by
    rcases hj with rfl | rfl <;> simp
  rcases hC.mem_poles hjV hja hjb with hjK | hjK
  · have := eq_of_closed hR.connm (fun x hx => hC.ne_of_mem (Or.inl hx)) (Finset.singleton_subset_iff.mpr hjK)
      (Finset.singleton_nonempty j) hcl
    exact hncap (Or.inl (this ▸ hjS))
  · have := eq_of_closed hR.connp (fun x hx => hC.ne_of_mem (Or.inr hx)) (Finset.singleton_subset_iff.mpr hjK)
      (Finset.singleton_nonempty j) hcl
    exact hncap (Or.inr (this ▸ hjS))

/-- The joints of a block have two neighbours. -/
theorem IsBlockU.nbrs_joint {G : UMultigraph V} {j₁ j₂ j : V} (hB : IsBlockU G j₁ j₂) (hj : j = j₁ ∨ j = j₂) :
    ∃ n n' : V, nbrs G j = {n, n'} := by
  have h : Multiset.card (nbrs G j) = 2 := by
    rw [card_nbrs]; rcases hj with rfl | rfl
    exacts [hB.2.2.2.1, hB.2.2.2.2.1]
  exact Multiset.card_eq_two.mp h

/-- The added bonds of a deletion are not loops. -/
theorem RungCore.rungAdds_count_diag {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) (v : V) : (rungAdds xm xp ym yp μ).count s(v, v) = 0 := by
  have h1 := hR.xm_ne_xp
  have h2 := hR.ym_ne_yp
  have h3 : xm ≠ yp := fun h => hR.not_mem_both hR.xm_mem (h ▸ hR.yp_mem)
  have h4 : xp ≠ ym := fun h => hR.not_mem_both hR.ym_mem (h ▸ hR.xp_mem)
  have hne : ∀ {x y : V}, x ≠ y → s(v, v) ≠ s(x, y) := fun hxy h => by
    rcases Sym2.eq_iff.mp h with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact hxy (h5.symm.trans h6)
    · exact hxy (h6.symm.trans h5)
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair]
    rw [if_neg (hne h1), if_neg (hne h2)]
  · simp only [rungAdds, if_true, count_pair]
    rw [if_neg (hne h3), if_neg (hne h4)]

theorem RungCore.loopless_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore G a b xm xp ym yp Km Kp) (hl : G.Loopless) (μ : Bool) :
    (rungDel G a b xm xp ym yp μ).Loopless := by
  intro v
  rw [rungDel_mult]
  split_ifs
  · rfl
  · rw [hl, hR.rungAdds_count_diag]

/-- A cross bond of a deletion at `u ∈ Km` has multiplicity at most `1` unless `u` carries both rails. -/
theorem RungCore.rungAdds_count_cross_le {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) {u w : V} (hu : u ∈ Km) (hw : w ∈ Kp)
    (h : ¬ (u = xm ∧ u = ym)) : (rungAdds xm xp ym yp μ).count s(u, w) ≤ 1 := by
  have hux : u ≠ xp := fun h => hR.not_mem_both hu (h ▸ hR.xp_mem)
  have huy : u ≠ yp := fun h => hR.not_mem_both hu (h ▸ hR.yp_mem)
  have key : ∀ {x y : V}, y ∈ Kp → s(u, w) = s(x, y) → u = x := fun hy h => by
    rcases Sym2.eq_iff.mp h with ⟨h5, _⟩ | ⟨h5, _⟩
    · exact h5
    · exact absurd (h5 ▸ hy) (fun h' => hR.not_mem_both hu h')
  cases μ
  · simp only [rungAdds, Bool.false_eq_true, if_false, count_pair]
    by_cases h1 : s(u, w) = s(xm, xp)
    · by_cases h2 : s(u, w) = s(ym, yp)
      · exact absurd ⟨key hR.xp_mem h1, key hR.yp_mem h2⟩ h
      · rw [if_pos h1, if_neg h2]
    · rw [if_neg h1]; split_ifs <;> omega
  · simp only [rungAdds, if_true, count_pair]
    have h2' : s(u, w) = s(xp, ym) → u = ym := fun h' => key hR.xp_mem (h'.trans Sym2.eq_swap)
    by_cases h1 : s(u, w) = s(xm, yp)
    · by_cases h2 : s(u, w) = s(xp, ym)
      · exact absurd ⟨key hR.yp_mem h1, h2' h2⟩ h
      · rw [if_pos h1, if_neg h2]
    · rw [if_neg h1]; split_ifs <;> omega

/-- The deleted graph of a 2-cut rung (with connected poles) is connected. -/
theorem IsRungAt.connected_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : IsRungAt G a b xm xp ym yp Km Kp) (μ : Bool) : Connected (rungDel G a b xm xp ym yp μ) := by
  have hC := hR.toCore
  set G' := rungDel G a b xm xp ym yp μ
  have hX : ∀ x, x ∈ G'.verts ↔ x ∈ Km ∨ x ∈ Kp := by
    intro x; show x ∈ (rungDel G a b xm xp ym yp μ).verts ↔ _
    rw [hC.verts_rungDel, ← hC.union, Finset.mem_union]
  have hlift : ∀ {K : Finset V}, (K = Km ∨ K = Kp) → ∀ {u v},
      Relation.ReflTransGen (AdjIn G K) u v → Relation.ReflTransGen (AdjIn G' G'.verts) u v := by
    intro K hK u v h
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) u v h
    obtain ⟨hx, hy, hm⟩ := hxy
    have hxy' : (x ∈ Km ∧ y ∈ Km) ∨ (x ∈ Kp ∧ y ∈ Kp) := by rcases hK with rfl | rfl <;> tauto
    refine ⟨(hX x).mpr (by tauto), (hX y).mpr (by tauto), ?_⟩
    rw [show G' = rungDel G a b xm xp ym yp μ from rfl, hC.rungDel_mult_same μ hxy']
    exact hm
  have hsymm : ∀ {u v}, Relation.ReflTransGen (AdjIn G' G'.verts) u v →
      Relation.ReflTransGen (AdjIn G' G'.verts) v u := by
    intro u v h
    induction h with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨h1, h2, h3⟩ := hst
      exact .head ⟨h2, h1, by rw [Sym2.eq_swap]; exact h3⟩ ih
  set z := if μ then yp else xp with hz
  have hzK : z ∈ Kp := by cases μ <;> simp [hz, hC.xp_mem, hC.yp_mem]
  have hcross : AdjIn G' G'.verts xm z := by
    refine ⟨(hX xm).mpr (Or.inl hC.xm_mem), (hX z).mpr (Or.inr hzK), ?_⟩
    rw [show G' = rungDel G a b xm xp ym yp μ from rfl, hC.rungDel_mult_cross hC.xm_mem hzK]
    apply Multiset.count_ne_zero.mpr
    cases μ <;> simp [hz, rungAdds]
  have hmp : ∀ u ∈ Km, ∀ w ∈ Kp, Relation.ReflTransGen (AdjIn G' G'.verts) u w := fun u hu w hw =>
    ((hlift (Or.inl rfl) (hR.connm u hu xm hC.xm_mem)).tail hcross).trans
      (hlift (Or.inr rfl) (hR.connp z hzK w hw))
  intro u hu w hw
  rcases (hX u).mp hu with hu | hu <;> rcases (hX w).mp hw with hw | hw
  · exact hlift (Or.inl rfl) (hR.connm u hu w hw)
  · exact hmp u hu w hw
  · exact hsymm (hmp w hw u hu)
  · exact hlift (Or.inr rfl) (hR.connp u hu w hw)

/-- A rail end is adjacent to its rung atom. -/
theorem RungCore.mem_nbrs_of_rail {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore G a b xm xp ym yp Km Kp) {j : V} (hja : j ≠ a) (hjb : j ≠ b) :
    ((j = xm ∨ j = xp) → a ∈ nbrs G j) ∧ ((j = ym ∨ j = yp) → b ∈ nbrs G j) := by
  constructor
  · intro h
    apply Multiset.count_pos.mp
    rw [count_nbrs, if_pos hR.a_verts, if_neg hja, Sym2.eq_swap, hR.mult_a, if_neg hjb, if_pos h]; omega
  · intro h
    apply Multiset.count_pos.mp
    rw [count_nbrs, if_pos hR.b_verts, if_neg hjb, Sym2.eq_swap, hR.mult_b, if_neg hja, if_pos h]; omega

private theorem cap_of_closed {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : IsRungAt G a b xm xp ym yp Km Kp) {S : Finset V} (hS : S ⊆ {j₁, j₂}) (hne : S.Nonempty)
    (hcl : ∀ u ∈ S, ∀ w, G.mult s(u, w) ≠ 0 → w ∈ S ∨ w = a ∨ w = b) (hSK : S ⊆ Km ∨ S ⊆ Kp) :
    IsCapAt j₁ j₂ Km Kp := by
  have hC := hR.toCore
  rcases hSK with h | h
  · exact Or.inl ((eq_of_closed hR.connm (fun x hx => hC.ne_of_mem (Or.inl hx)) h hne hcl) ▸ hS)
  · exact Or.inr ((eq_of_closed hR.connp (fun x hx => hC.ne_of_mem (Or.inr hx)) h hne hcl) ▸ hS)

/-- Smoothing `j₁` leaves no loop at `j₂` when `σ < 2`. -/
theorem smooth_loop_j₂ {G : UMultigraph V} {j₁ j₂ n1 n1' : V} (hl : G.Loopless) (hj : j₁ ≠ j₂)
    (hσ : G.mult s(j₁, j₂) < 2) (h1 : nbrs G j₁ = {n1, n1'}) : (smooth G j₁ n1 n1').mult s(j₂, j₂) = 0 := by
  have hσc : G.mult s(j₁, j₂) = ({n1, n1'} : Multiset V).count j₂ := mult_of_nbrs_eq h1 (Ne.symm hj)
  rw [smooth_mult_at G (Ne.symm hj), if_neg (Ne.symm hj), hl, zero_add, if_neg]
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  · rw [← h3, ← h4, count_pair_self] at hσc; simp at hσc; omega

/-- After smoothing `j₁`, the second joint is not adjacent to both rung atoms (else a pole would be a cap). -/
theorem IsRungAt.not_both_after_smooth {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp n1 n1' n2 n2' : V}
    {Km Kp : Finset V} (hR : IsRungAt G a b xm xp ym yp Km Kp) (hncap : ¬ IsCapAt j₁ j₂ Km Kp)
    (hl : G.Loopless) (hj : j₁ ≠ j₂) (hj₁V : j₁ ∈ G.verts) (hj₂V : j₂ ∈ G.verts) (hj₁a : j₁ ≠ a)
    (hj₁b : j₁ ≠ b) (hj₂a : j₂ ≠ a) (hj₂b : j₂ ≠ b) (hσ : G.mult s(j₁, j₂) < 2) (h1 : nbrs G j₁ = {n1, n1'})
    (h2 : nbrs (smooth G j₁ n1 n1') j₂ = {n2, n2'}) :
    ¬ (a ∈ nbrs (smooth G j₁ n1 n1') j₂ ∧ b ∈ nbrs (smooth G j₁ n1 n1') j₂) := by
  rintro ⟨ha, hb⟩
  have hC := hR.toCore
  have hl1 := smooth_loop_j₂ hl hj hσ h1
  -- the neighbours of `j₂` after smoothing are `a, b`
  rw [h2] at ha hb
  obtain ⟨w, hw⟩ := pair_eq_of_mem ha
  rw [hw] at hb h2
  have hwb : w = b := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb
    rcases hb with h | h
    · exact absurd h.symm hR.ne
    · exact h.symm
  rw [hwb] at h2
  have hcl1 : ∀ w, (smooth G j₁ n1 n1').mult s(j₂, w) ≠ 0 → w = a ∨ w = b := nbrs_closed h2 hl1
  have hG₁ : ∀ w, w ≠ j₁ → G.mult s(j₂, w) ≤ (smooth G j₁ n1 n1').mult s(j₂, w) := by
    intro w hw
    rw [smooth_mult_at G (Ne.symm hj), if_neg hw]; omega
  have hσc : G.mult s(j₁, j₂) = ({n1, n1'} : Multiset V).count j₂ := mult_of_nbrs_eq h1 (Ne.symm hj)
  by_cases hj₂n : j₂ ∈ ({n1, n1'} : Multiset V)
  · obtain ⟨x, hx⟩ := pair_eq_of_mem hj₂n
    rw [hx] at h1 hσc
    have hxj₁ := (nbrs_mem_ne hl h1).2
    have hs : s(n1, n1') = s(j₂, x) := sym2_eq_of_pair_eq hx
    have hadj : G.mult s(j₁, j₂) ≠ 0 := by rw [hσc, count_pair_self]; omega
    refine hncap (cap_of_closed hR (S := {j₁, j₂}) (by simp) (by simp) ?_ ?_)
    · intro u hu w' hw'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · rcases nbrs_closed h1 (hl u) w' hw' with rfl | rfl
        · simp
        · right
          apply hcl1
          rw [smooth_mult_at G (Ne.symm hj), if_neg hxj₁, hs, if_pos rfl]; omega
      · by_cases hw'1 : w' = j₁
        · subst hw'1; simp
        · right
          exact hcl1 w' (by have := hG₁ w' hw'1; omega)
    · rcases hC.mem_poles hj₁V hj₁a hj₁b with hK | hK
      · left
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hK
        · exact hC.mem_Km_of_mult hK hadj hj₂a hj₂b
      · right
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hK
        · exact hC.swapPoles.mem_Km_of_mult hK hadj hj₂a hj₂b
  · have hσ0 : G.mult s(j₁, j₂) = 0 := by rw [hσc]; exact Multiset.count_eq_zero.mpr hj₂n
    refine hncap (cap_of_closed hR (S := {j₂}) (by simp) (by simp) ?_ ?_)
    · intro u hu w' hw'
      rw [Finset.mem_singleton] at hu; subst hu
      by_cases hw'1 : w' = j₁
      · subst hw'1; rw [Sym2.eq_swap, hσ0] at hw'; exact absurd rfl hw'
      · right; exact hcl1 w' (by have := hG₁ w' hw'1; omega)
    · rcases hC.mem_poles hj₂V hj₂a hj₂b with hK | hK
      · exact Or.inl (Finset.singleton_subset_iff.mpr hK)
      · exact Or.inr (Finset.singleton_subset_iff.mpr hK)

/-- `σ` of the deleted graph stays below `2`. -/
theorem RungCore.sigma_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore G a b xm xp ym yp Km Kp) (μ : Bool) {j₁ j₂ : V} (hj₁ : j₁ ∈ Km ∨ j₁ ∈ Kp)
    (hj₂ : j₂ ∈ Km ∨ j₂ ∈ Kp) (hσ : G.mult s(j₁, j₂) < 2) (h1 : ¬ (j₁ = xm ∧ j₁ = ym))
    (h2 : ¬ (j₂ = xm ∧ j₂ = ym)) : (rungDel G a b xm xp ym yp μ).mult s(j₁, j₂) < 2 := by
  rcases hj₁ with hj₁ | hj₁ <;> rcases hj₂ with hj₂ | hj₂
  · rw [hR.rungDel_mult_same μ (Or.inl ⟨hj₁, hj₂⟩)]; exact hσ
  · rw [hR.rungDel_mult_cross hj₁ hj₂]
    have := hR.rungAdds_count_cross_le μ hj₁ hj₂ h1; omega
  · rw [Sym2.eq_swap, hR.rungDel_mult_cross hj₂ hj₁]
    have := hR.rungAdds_count_cross_le μ hj₂ hj₁ h2; omega
  · rw [hR.rungDel_mult_same μ (Or.inr ⟨hj₁, hj₂⟩)]; exact hσ

/-- **N2 Lemma 1.9(1)** (path-wise; M4 §2.2 `TVine.isTVine_deleteRung`): deleting a deletable rung of a T-vine,
with either matching, gives a T-vine with the same joints. -/
theorem isTVineU_rungDel {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (hT : IsTVineU G j₁ j₂) (hD : IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp) (μ : Bool) :
    IsTVineU (rungDel G a b xm xp ym yp μ) j₁ j₂ := by
  have hl := hT.loopless
  obtain ⟨hB, hm2, C, hC, hRT⟩ := hT
  obtain ⟨⟨hR, haj₁, haj₂, hbj₁, hbj₂⟩, hncap⟩ := hD
  have hRc := hR.toCore
  have hBB := hB
  obtain ⟨hj₁V, hj₂V, hj, hd₁, hd₂, hd, -⟩ := hB
  have hσ := hC.1
  have hCl := hC.2.2.1
  obtain ⟨n1, n1', n2, n2', h1, h2, hCeq⟩ := hC.eq_smooth hl hj
  have hab1 := hR.not_both_of_joint hncap (Or.inl rfl) hj₁V (Ne.symm haj₁) (Ne.symm hbj₁) (hl j₁) h1
  obtain ⟨c1, c1', h2G⟩ := hBB.nbrs_joint (Or.inr rfl)
  have hab2G := hR.not_both_of_joint hncap (Or.inr rfl) hj₂V (Ne.symm haj₂) (Ne.symm hbj₂) (hl j₂) h2G
  obtain ⟨r1, r2, r3, r4, hC1, hμ1⟩ :=
    smooth_rungDel_step hRc hj₁V (Ne.symm haj₁) (Ne.symm hbj₁) (hl j₁) h1 hab1
  have hn1V := nbrs_mem_verts h1
  have hj₂V1 : j₂ ∈ (smooth G j₁ n1 n1').verts := by
    rw [smooth_verts hn1V.1 hn1V.2]; exact Finset.mem_erase.mpr ⟨Ne.symm hj, hj₂V⟩
  have hab2 := hR.not_both_after_smooth hncap hl hj hj₁V hj₂V (Ne.symm haj₁) (Ne.symm hbj₁) (Ne.symm haj₂)
    (Ne.symm hbj₂) hσ h1 h2
  obtain ⟨s1, s2, s3, s4, hC2, hμ2⟩ := smooth_rungDel_step hC1 hj₂V1 (Ne.symm haj₂) (Ne.symm hbj₂)
    (smooth_loop_j₂ hl hj hσ h1) h2 hab2
  obtain ⟨m1, m1', hm1, hc1⟩ := hμ1 μ
  obtain ⟨m2, m2', hm2', hc2⟩ := hμ2 μ
  rw [← hc1] at hm2' hc2
  rw [← hCeq] at hC2 hc2
  have hVR : ∀ v, v ∈ (rungDel G a b xm xp ym yp μ).verts ↔ v ∈ G.verts ∧ v ≠ a ∧ v ≠ b := by
    intro v; rw [hRc.verts_rungDel]; simp only [Finset.mem_erase]; tauto
  have hpoles : ∀ v, v ∈ G.verts → v ≠ a → v ≠ b → v ∈ Km ∨ v ∈ Kp := fun v h1 h2 h3 => hRc.mem_poles h1 h2 h3
  have hrail : ∀ j, j ≠ a → j ≠ b → ¬ (a ∈ nbrs G j ∧ b ∈ nbrs G j) → ¬ (j = xm ∧ j = ym) := by
    intro j hja hjb hab h
    exact hab ⟨(hRc.mem_nbrs_of_rail hja hjb).1 (Or.inl h.1), (hRc.mem_nbrs_of_rail hja hjb).2 (Or.inl h.2)⟩
  refine ⟨⟨(hVR j₁).mpr ⟨hj₁V, Ne.symm haj₁, Ne.symm hbj₁⟩, (hVR j₂).mpr ⟨hj₂V, Ne.symm haj₂, Ne.symm hbj₂⟩,
    hj, by rw [hRc.deg_rungDel μ (Ne.symm haj₁) (Ne.symm hbj₁)]; exact hd₁,
    by rw [hRc.deg_rungDel μ (Ne.symm haj₂) (Ne.symm hbj₂)]; exact hd₂, ?_, hR.connected_rungDel μ⟩, ?_,
    rungDel C a b s1 s2 s3 s4 μ, ?_, (reducesToT_rungDel_iff hC2 μ).mp hRT⟩
  · intro v hv hv1 hv2
    obtain ⟨hvV, hva, hvb⟩ := (hVR v).mp hv
    rw [hRc.deg_rungDel μ hva hvb]; exact hd v hvV hv1 hv2
  · intro u hu v hv huv
    obtain ⟨huV, hua, hub⟩ := (hVR u).mp hu
    obtain ⟨hvV, hva, hvb⟩ := (hVR v).mp hv
    rcases hpoles u huV hua hub with hu' | hu' <;> rcases hpoles v hvV hva hvb with hv' | hv'
    · rw [hRc.rungDel_mult_same μ (Or.inl ⟨hu', hv'⟩)]; exact hm2 u huV v hvV huv
    · exact hRc.rungDel_mult_le μ hu' hv'
    · rw [Sym2.eq_swap]; exact hRc.rungDel_mult_le μ hv' hu'
    · rw [hRc.rungDel_mult_same μ (Or.inr ⟨hu', hv'⟩)]; exact hm2 u huV v hvV huv
  · rw [← hc2]
    refine isClosureU_of_smooth (hRc.loopless_rungDel hl μ) hj ?_ hm1 hm2' ?_
    · exact hRc.sigma_rungDel μ (hpoles j₁ hj₁V (Ne.symm haj₁) (Ne.symm hbj₁))
        (hpoles j₂ hj₂V (Ne.symm haj₂) (Ne.symm hbj₂)) hσ (hrail j₁ (Ne.symm haj₁) (Ne.symm hbj₁) hab1)
        (hrail j₂ (Ne.symm haj₂) (Ne.symm hbj₂) hab2G)
    · rw [hc2]; exact hC2.loopless_rungDel hCl μ

end WaveTurbulence.TVine.Core

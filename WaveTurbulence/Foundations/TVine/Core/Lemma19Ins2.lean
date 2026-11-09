/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma19Ins

/-!
# N2 Lemma 1.9(2): rung insertion keeps a T-vine a T-vine (path-wise)

`rungInsertion_holds : RungInsertionStatement`. The inserted graph is a block (`InsData.isBlockU`) with the new rung
a deletable 2-cut rung; its closure is built by smoothing the joints (`isClosureU_of_smooth`), and smoothing commutes
with the crossed deletion (`smooth_rungDel_step`, as in N2 Lemma 1.9(1)), so the closure minus the rung is the closure
of the original T-vine; N2 Lemma 1.5 (path-wise, Lemma 5″) transfers `→* T` back.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- Smoothing depends only on the multiset of the two neighbours. -/
theorem smooth_congr_pair (G : UMultigraph V) (j : V) {n n' m m' : V}
    (hpair : ({n, n'} : Multiset V) = {m, m'}) : smooth G j n n' = smooth G j m m' := by
  unfold smooth; rw [sym2_eq_of_pair_eq hpair]

namespace InsData

variable {G : UMultigraph V} {X : Finset V} {p q p' q' u v : V} (h : InsData G X p q p' q' u v)
include h

theorem deg_u : deg (insertRung G p q p' q' u v) u = 4 := by
  unfold deg
  rw [h.verts]
  simp only [h.mult_u, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [h.huv, Ne.symm (h.ne_u h.pV), Ne.symm (h.ne_u h.qV), h.pV, h.qV]

theorem deg_v : deg (insertRung G p q p' q' u v) v = 4 := by
  unfold deg
  rw [h.verts]
  simp only [h.mult_v, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Ne.symm h.huv, Ne.symm (h.ne_v h.p'V), Ne.symm (h.ne_v h.q'V), h.p'V, h.q'V]

theorem connected {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) : Connected (insertRung G p q p' q' u v) := by
  have hR := h.isRungAt hB
  set Gi := insertRung G p q p' q' u v with hGi
  have hsymm : ∀ {a b : V}, Relation.ReflTransGen (AdjIn Gi Gi.verts) a b →
      Relation.ReflTransGen (AdjIn Gi Gi.verts) b a := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨h1, h2, h3⟩ := hst
      exact .head ⟨h2, h1, by rw [Sym2.eq_swap]; exact h3⟩ ih
  have hlift : ∀ {K : Finset V}, K ⊆ Gi.verts → ConnOn Gi K → ∀ a ∈ K, ∀ b ∈ K,
      Relation.ReflTransGen (AdjIn Gi Gi.verts) a b := by
    intro K hK hc a ha b hb
    exact Relation.ReflTransGen.mono (fun x y hxy => ⟨hK hxy.1, hK hxy.2.1, hxy.2.2⟩) a b (hc a ha b hb)
  have hGV : ∀ {x}, x ∈ G.verts → x ∈ Gi.verts := fun hx => h.mem_verts.mpr (Or.inr (Or.inr hx))
  have hXs : X ⊆ Gi.verts := fun x hx => hGV (h.hX hx)
  have hYs : G.verts \ X ⊆ Gi.verts := fun x hx => hGV (Finset.mem_sdiff.mp hx).1
  have hfrom : ∀ w ∈ Gi.verts, Relation.ReflTransGen (AdjIn Gi Gi.verts) u w := by
    intro w hw
    rcases h.mem_verts.mp hw with hwu | hwv | hwV
    · rw [hwu]
    · rw [hwv]; exact .single ⟨hR.a_mem, hR.b_mem, by rw [hR.mult_ab]; omega⟩
    · by_cases hwX : w ∈ X
      · exact (Relation.ReflTransGen.single ⟨hR.a_mem, hXs h.hp, by rw [hR.a_xm]; omega⟩).trans
          (hlift hXs hR.connm p h.hp w hwX)
      · have hwY : w ∈ G.verts \ X := Finset.mem_sdiff.mpr ⟨hwV, hwX⟩
        exact (Relation.ReflTransGen.single ⟨hR.a_mem, hYs h.hq, by rw [hR.a_xp]; omega⟩).trans
          (hlift hYs hR.connp q h.hq w hwY)
  intro a ha b hb
  exact (hsymm (hfrom a ha)).trans (hfrom b hb)

/-- The inserted graph of a block is a block with the same joints. -/
theorem isBlockU {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) : IsBlockU (insertRung G p q p' q' u v) j₁ j₂ := by
  have hRc := (h.isRungAt hB).toCore
  have hdel := h.rungDel_eq hB
  have hconn := h.connected hB
  have hdeg : ∀ w, w ≠ u → w ≠ v → deg (insertRung G p q p' q' u v) w = deg G w := by
    intro w hwu hwv
    rw [← hRc.deg_rungDel false hwu hwv, hdel]
  obtain ⟨hj₁V, hj₂V, hj, hd₁, hd₂, hd, -⟩ := hB
  refine ⟨h.mem_verts.mpr (Or.inr (Or.inr hj₁V)), h.mem_verts.mpr (Or.inr (Or.inr hj₂V)), hj,
    by rw [hdeg j₁ (h.ne_u hj₁V) (h.ne_v hj₁V)]; exact hd₁,
    by rw [hdeg j₂ (h.ne_u hj₂V) (h.ne_v hj₂V)]; exact hd₂, fun w hw hw1 hw2 => ?_,
    hconn⟩
  rcases h.mem_verts.mp hw with hwu | hwv | hwV
  · rw [hwu]; exact h.deg_u
  · rw [hwv]; exact h.deg_v
  · rw [hdeg w (h.ne_u hwV) (h.ne_v hwV)]; exact hd w hwV hw1 hw2

end InsData

/-- **N2 Lemma 1.9(2)** (rung insertion, applied undirected; REF2). -/
theorem rungInsertion_holds : RungInsertionStatement.{u} := by
  intro V _ G j₁ j₂ X p q p' q' u v hT hX hc hp hp' hq hq' hm hm' hsame hiX hiY hu hv huv
  have hD : InsData G X p q p' q' u v := ⟨hX, hc, hp, hp', hq, hq', hm, hm', hsame, hu, hv, huv⟩
  have hl := hT.loopless
  obtain ⟨hB, hm2, C₀, hC₀, hRT⟩ := hT
  have hj₁V := hB.1
  have hj₂V := hB.2.1
  have hj := hB.2.2.1
  set Gi := insertRung G p q p' q' u v with hGi
  have hR : IsRungAt Gi u v p q p' q' X (G.verts \ X) := hD.isRungAt hB
  have hRc := hR.toCore
  have hdel : rungDel Gi u v p q p' q' false = G := hD.rungDel_eq hB
  have hlGi : Gi.Loopless := hD.loopless hl
  have hBGi : IsBlockU Gi j₁ j₂ := hD.isBlockU hB
  have hm2Gi := hD.mult_le_two hm2
  have hj₁u : j₁ ≠ u := hD.ne_u hj₁V
  have hj₁v : j₁ ≠ v := hD.ne_v hj₁V
  have hj₂u : j₂ ≠ u := hD.ne_u hj₂V
  have hj₂v : j₂ ≠ v := hD.ne_v hj₂V
  have hncap : ¬ IsCapAt j₁ j₂ X (G.verts \ X) := by
    rintro (hc' | hc')
    · obtain ⟨i, hi, hi1, hi2⟩ := hiX
      have := hc' hi; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
    · obtain ⟨i, hi, hi1, hi2⟩ := hiY
      have := hc' hi; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  have hσGi : Gi.mult s(j₁, j₂) < 2 := by
    rw [hGi, hD.mult_old hj₁u hj₁v hj₂u hj₂v]
    have := hC₀.1; omega
  refine ⟨?_, ⟨⟨hR, Ne.symm hj₁u, Ne.symm hj₂u, Ne.symm hj₁v, Ne.symm hj₂v⟩, hncap⟩, hdel⟩
  -- the closure of `Gi`, built by smoothing the joints
  have hj₁Gi : j₁ ∈ Gi.verts := hBGi.1
  have hj₂Gi : j₂ ∈ Gi.verts := hBGi.2.1
  obtain ⟨m1, m1', h1⟩ := hBGi.nbrs_joint (Or.inl rfl)
  have hab1 := hR.not_both_of_joint hncap (Or.inl rfl) hj₁Gi hj₁u hj₁v (hlGi j₁) h1
  obtain ⟨r1, r2, r3, r4, hC1, hμ1⟩ := smooth_rungDel_step hRc hj₁Gi hj₁u hj₁v (hlGi j₁) h1 hab1
  have hdeg2 : deg (smooth Gi j₁ m1 m1') j₂ = 2 := by
    rw [deg_smooth (hlGi j₁) h1 (Ne.symm hj)]; exact hBGi.2.2.2.2.1
  obtain ⟨m2, m2', h2⟩ : ∃ m2 m2', nbrs (smooth Gi j₁ m1 m1') j₂ = {m2, m2'} :=
    Multiset.card_eq_two.mp (by rw [card_nbrs]; exact hdeg2)
  have hab2 := hR.not_both_after_smooth hncap hlGi hj hj₁Gi hj₂Gi hj₁u hj₁v hj₂u hj₂v hσGi h1 h2
  have hn1V := nbrs_mem_verts h1
  have hj₂V1 : j₂ ∈ (smooth Gi j₁ m1 m1').verts := by
    rw [smooth_verts hn1V.1 hn1V.2]; exact Finset.mem_erase.mpr ⟨Ne.symm hj, hj₂Gi⟩
  obtain ⟨s1, s2, s3, s4, hC2, hμ2⟩ :=
    smooth_rungDel_step hC1 hj₂V1 hj₂u hj₂v (smooth_loop_j₂ hlGi hj hσGi h1) h2 hab2
  obtain ⟨k1, k1', hk1, hc1⟩ := hμ1 false
  obtain ⟨k2, k2', hk2, hc2⟩ := hμ2 false
  rw [hdel] at hk1 hc1
  rw [← hc1] at hk2 hc2
  -- compare with the closure of `G`
  obtain ⟨n1, n1', n2, n2', g1, g2, hC₀eq⟩ := hC₀.eq_smooth hl hj
  rw [smooth_congr_pair G j₁ (hk1.symm.trans g1)] at hk2 hc2
  have hEq : rungDel (smooth (smooth Gi j₁ m1 m1') j₂ m2 m2') u v s1 s2 s3 s4 false = C₀ := by
    rw [← hc2, smooth_congr_pair _ j₂ (hk2.symm.trans g2), hC₀eq]
  have hC₀l : C₀.Loopless := hC₀.2.2.1
  -- the closure of `Gi` is loopless
  have hCl : (smooth (smooth Gi j₁ m1 m1') j₂ m2 m2').Loopless := by
    intro w
    by_cases hwu : w = u
    · rw [hwu, hC2.mult_a, if_neg huv, if_neg]
      rintro (e | e)
      · exact (hC2.ne_of_mem (Or.inl hC2.xm_mem)).1 e.symm
      · exact (hC2.ne_of_mem (Or.inr hC2.xp_mem)).1 e.symm
    by_cases hwv : w = v
    · rw [hwv, hC2.mult_b, if_neg (Ne.symm huv), if_neg]
      rintro (e | e)
      · exact (hC2.ne_of_mem (Or.inl hC2.ym_mem)).2 e.symm
      · exact (hC2.ne_of_mem (Or.inr hC2.yp_mem)).2 e.symm
    have hw : (rungDel (smooth (smooth Gi j₁ m1 m1') j₂ m2 m2') u v s1 s2 s3 s4 false).mult s(w, w) =
        C₀.mult s(w, w) := by rw [hEq]
    rw [rungDel_mult, if_neg (by
      rintro (e | e) <;> rcases Sym2.mem_iff.mp e with e' | e'
      · exact hwu e'.symm
      · exact hwu e'.symm
      · exact hwv e'.symm
      · exact hwv e'.symm), hC2.rungAdds_count_diag, add_zero, hC₀l w] at hw
    exact hw
  refine ⟨hBGi, hm2Gi, smooth (smooth Gi j₁ m1 m1') j₂ m2 m2',
    isClosureU_of_smooth hlGi hj hσGi h1 h2 hCl, ?_⟩
  exact (reducesToT_rungDel_iff hC2 false).mpr (by rw [hEq]; exact hRT)

end WaveTurbulence.TVine.Core

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.VineII2

/-!
# Deleting a rung of vine (II)

* `adds_false`, `adds_true`: the two bonds added by a rung deletion, read on the uniform ladder (for the crossed
  matching, the poles force the rails to pair up on the same side of the rung);
* `vineII_rungDel`: deleting a rung (off the joints) of a vine (II) gives a vine (II), except for the Q-block
  `{p, a, b, q}`, where it gives the double bond `p = q` (vine (I)) and the poles are `{p}`, `{q}`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

/-! ## Arithmetic on the uniform ladder -/

theorem isLadRung_symm {M u w : ℕ} (h : IsLadRung M u w) : IsLadRung M w u := by
  unfold IsLadRung at *; omega

theorem isLadRung_of_count_two {M x y : ℕ} (h : (ladMS M).count s(x, y) = 2) : IsLadRung M x y := by
  rw [count_ladMS] at h
  by_contra hc
  rw [if_neg hc] at h
  split_ifs at h <;> omega

theorem ladSig_of_lt {r U : ℕ} (tw : Bool) (h : U < r) : ladSig r tw U = U := by
  unfold ladSig; rw [if_pos h]

/-- The straight matching adds the two rail continuations. -/
theorem adds_false {M r u w Xm Xp Ym Yp : ℕ} (huw : (u = r ∧ w = r + 1) ∨ (u = r + 1 ∧ w = r))
    (hXm : Xm = ladLo u ∨ Xm = ladHi M u) (hXp : Xp = ladLo u ∨ Xp = ladHi M u) (hX : Xm ≠ Xp)
    (hYm : Ym = ladLo w ∨ Ym = ladHi M w) (hYp : Yp = ladLo w ∨ Yp = ladHi M w) (hY : Ym ≠ Yp) :
    (s(Xm, Xp) = ladAdd₁ M r false ∧ s(Ym, Yp) = ladAdd₂ M r false) ∨
      (s(Xm, Xp) = ladAdd₂ M r false ∧ s(Ym, Yp) = ladAdd₁ M r false) := by
  simp only [ladAdd₁, ladAdd₂, Bool.false_eq_true, ↓reduceIte]
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hXm with rfl | rfl <;> rcases hXp with rfl | rfl <;> rcases hYm with rfl | rfl <;>
    rcases hYp with rfl | rfl <;>
    first
      | exact absurd rfl hX
      | exact absurd rfl hY
      | (left; constructor <;> first | rfl | exact Sym2.eq_swap)
      | (right; constructor <;> first | rfl | exact Sym2.eq_swap)

/-- The crossed matching adds the two crossed bonds (the poles force `xm, ym` onto the same side). -/
theorem adds_true {M r u w Xm Xp Ym Yp : ℕ} (hr2 : 2 ≤ r) (hre : r % 2 = 0) (hrM : r ≤ 2 * M + 2)
    (huw : (u = r ∧ w = r + 1) ∨ (u = r + 1 ∧ w = r))
    (hXm : Xm = ladLo u ∨ Xm = ladHi M u) (hXp : Xp = ladLo u ∨ Xp = ladHi M u) (hX : Xm ≠ Xp)
    (hYm : Ym = ladLo w ∨ Ym = ladHi M w) (hYp : Yp = ladLo w ∨ Yp = ladHi M w) (hY : Ym ≠ Yp)
    (h1 : Xm ≠ Yp) (h2 : Xp ≠ Ym) (h3 : (ladMS M).count s(Xm, Yp) = 0)
    (h4 : (ladMS M).count s(Xp, Ym) = 0) :
    (s(Xm, Yp) = ladAdd₁ M r true ∧ s(Xp, Ym) = ladAdd₂ M r true) ∨
      (s(Xm, Yp) = ladAdd₂ M r true ∧ s(Xp, Ym) = ladAdd₁ M r true) := by
  have hr1 : IsLadRung M r (r + 1) := by unfold IsLadRung; omega
  have hr1' : IsLadRung M (r + 1) r := by unfold IsLadRung; omega
  simp only [ladAdd₁, ladAdd₂, ↓reduceIte]
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hXm with rfl | rfl <;> rcases hXp with rfl | rfl <;> rcases hYm with rfl | rfl <;>
    rcases hYp with rfl | rfl <;>
    first
      | exact absurd rfl hX
      | exact absurd rfl hY
      | exact absurd h3 (ladLo_rung hr1 h1)
      | exact absurd h3 (ladLo_rung hr1' h1)
      | exact absurd h4 (ladLo_rung hr1 h2)
      | exact absurd h4 (ladLo_rung hr1' h2)
      | (left; constructor <;> first | rfl | exact Sym2.eq_swap)
      | (right; constructor <;> first | rfl | exact Sym2.eq_swap)

theorem ind_pair {Z A1 A2 B1 B2 : Sym2 ℕ} (h : (A1 = B1 ∧ A2 = B2) ∨ (A1 = B2 ∧ A2 = B1)) :
    ((if Z = A1 then 1 else 0) + (if Z = A2 then 1 else 0) : ℕ) =
      (if Z = B1 then 1 else 0) + (if Z = B2 then 1 else 0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact add_comm _ _

/-! ## Graph-level plumbing -/

section Graph

variable {V : Type*} [DecidableEq V]

theorem count_pair_map {S : Finset V} {g : V → ℕ} (hinj : Set.InjOn g S) {x y c d e f : V} (hx : x ∈ S)
    (hy : y ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S) (hf : f ∈ S) :
    ({s(c, d), s(e, f)} : Multiset (Sym2 V)).count s(x, y) =
      (if s(g x, g y) = s(g c, g d) then 1 else 0) + (if s(g x, g y) = s(g e, g f) then 1 else 0) := by
  simp only [sym2_eq_iff_of_injOn hinj hx hy hc hd, sym2_eq_iff_of_injOn hinj hx hy he hf]
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, add_comm]

theorem not_mem_pair {a b x y : V} (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    ¬(a ∈ s(x, y) ∨ b ∈ s(x, y)) := by
  simp only [Sym2.mem_iff]
  rintro ((h | h) | (h | h))
  exacts [hxa h.symm, hya h.symm, hxb h.symm, hyb h.symm]

theorem poles_of_pair {Km Kp : Finset V} {p q xm xp : V} (hU : Km ∪ Kp = {p, q}) (hD : Disjoint Km Kp)
    (hxm : xm ∈ Km) (hxp : xp ∈ Kp) : (Km = {p} ∧ Kp = {q}) ∨ (Km = {q} ∧ Kp = {p}) := by
  have hmem : ∀ x, x ∈ Km ∨ x ∈ Kp ↔ x = p ∨ x = q := fun x => by
    rw [← Finset.mem_union, hU, Finset.mem_insert, Finset.mem_singleton]
  have hnb : ∀ x, x ∈ Km → x ∈ Kp → False := fun x h1 h2 => Finset.disjoint_left.mp hD h1 h2
  have hKm : ∀ x ∈ Km, x ≠ xp := fun x hx h => hnb x hx (h ▸ hxp)
  have hKp : ∀ x ∈ Kp, x ≠ xm := fun x hx h => hnb x (h ▸ hxm) hx
  have h1 := (hmem xm).mp (Or.inl hxm)
  have h2 := (hmem xp).mp (Or.inr hxp)
  have key : ∀ {s t : V}, (∀ x, x ∈ Km ∨ x ∈ Kp ↔ x = s ∨ x = t) → xm = s → xp = t →
      Km = {s} ∧ Kp = {t} := by
    intro s t hst hs ht
    subst hs ht
    constructor
    · ext x; rw [Finset.mem_singleton]; constructor
      · intro hx
        rcases (hst x).mp (Or.inl hx) with h | h
        · exact h
        · exact absurd h (hKm x hx)
      · rintro rfl; exact hxm
    · ext x; rw [Finset.mem_singleton]; constructor
      · intro hx
        rcases (hst x).mp (Or.inr hx) with h | h
        · exact absurd h (hKp x hx)
        · exact h
      · rintro rfl; exact hxp
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (hnb xm hxm (by rw [h1, ← h2]; exact hxp)).elim
  · exact Or.inl (key hmem h1 h2)
  · exact Or.inr (key (fun x => (hmem x).trans or_comm) h1 h2)
  · exact (hnb xm hxm (by rw [h1, ← h2]; exact hxp)).elim

/-- **Deleting a rung of vine (II)** (N2 1.14(c′), the vine-(II) case): the result is a vine (II), or — for
the Q-block — the double bond (vine (I)), with poles `{p}`, `{q}`. -/
theorem vineII_rungDel {X : UMultigraph V} {p q a b xm xp ym yp : V} {Km Kp : Finset V}
    (hX : IsVineXU .II X p q) (hR : RungCore X a b xm xp ym yp Km Kp)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (μ : Bool) :
    IsVineXU .II (rungDel X a b xm xp ym yp μ) p q ∨
      (X.verts = {p, a, b, q} ∧ IsVineXU .I (rungDel X a b xm xp ym yp μ) p q ∧
        ((Km = {p} ∧ Kp = {q}) ∨ (Km = {q} ∧ Kp = {p}))) := by
  obtain ⟨hB, M, g, hinj, himg, hpq, hmult⟩ := isVineXU_II_iff.mp hX
  have hB' := hB.rungDel_of_rungCore hR (Ne.symm hap) (Ne.symm hbp) (Ne.symm haq) (Ne.symm hbq) μ
  have hV' := hR.verts_rungDel μ
  have hpV : p ∈ X.verts := hB.1
  have hqV : q ∈ X.verts := hB.2.1
  have haV := hR.a_verts
  have hbV := hR.b_verts
  have hxm := hR.mem_verts (Or.inl hR.xm_mem)
  have hxp := hR.mem_verts (Or.inr hR.xp_mem)
  have hym := hR.mem_verts (Or.inl hR.ym_mem)
  have hyp := hR.mem_verts (Or.inr hR.yp_mem)
  have hlt : ∀ x ∈ X.verts, g x < 2 * M + 4 := fun x hx => by
    have := Finset.mem_image_of_mem g hx; rw [himg, Finset.mem_range] at this; exact this
  have hpre : ∀ U < 2 * M + 4, ∃ x ∈ X.verts, g x = U := fun U hU => by
    have : U ∈ X.verts.image g := by rw [himg, Finset.mem_range]; exact hU
    exact Finset.mem_image.mp this
  -- the rung `{a, b}` is a rung `{r, r + 1}` of the ladder
  have huw : IsLadRung M (g a) (g b) :=
    isLadRung_of_count_two (by rw [← hmult a haV b hbV, hR.mult_a b, if_pos rfl])
  have hwu : IsLadRung M (g b) (g a) := isLadRung_symm huw
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * (g a / 2) := ⟨_, rfl⟩
  have hrs : (g a = r ∧ g b = r + 1) ∨ (g a = r + 1 ∧ g b = r) := by unfold IsLadRung at huw; omega
  have hr2 : 2 ≤ r := by unfold IsLadRung at huw; omega
  have hre : r % 2 = 0 := by omega
  have hrM : r ≤ 2 * M + 2 := by unfold IsLadRung at huw; omega
  -- the rails at the rung
  have hXm : g xm = ladLo (g a) ∨ g xm = ladHi M (g a) := ladRail_of_rung huw (by
    rw [← hmult a haV xm hxm.1, hR.mult_a xm, if_neg hxm.2.2, if_pos (Or.inl rfl)])
  have hXp : g xp = ladLo (g a) ∨ g xp = ladHi M (g a) := ladRail_of_rung huw (by
    rw [← hmult a haV xp hxp.1, hR.mult_a xp, if_neg hxp.2.2, if_pos (Or.inr rfl)])
  have hYm : g ym = ladLo (g b) ∨ g ym = ladHi M (g b) := ladRail_of_rung hwu (by
    rw [← hmult b hbV ym hym.1, hR.mult_b ym, if_neg hym.2.1, if_pos (Or.inl rfl)])
  have hYp : g yp = ladLo (g b) ∨ g yp = ladHi M (g b) := ladRail_of_rung hwu (by
    rw [← hmult b hbV yp hyp.1, hR.mult_b yp, if_neg hyp.2.1, if_pos (Or.inr rfl)])
  have hX : g xm ≠ g xp := fun h => hR.xm_ne_xp (hinj hxm.1 hxp.1 h)
  have hY : g ym ≠ g yp := fun h => hR.ym_ne_yp (hinj hym.1 hyp.1 h)
  -- the added bonds, read on the ladder
  have hadd : ∀ x ∈ X.verts, ∀ y ∈ X.verts, (rungAdds xm xp ym yp μ).count s(x, y) =
      (if s(g x, g y) = ladAdd₁ M r μ then 1 else 0) + (if s(g x, g y) = ladAdd₂ M r μ then 1 else 0) := by
    intro x hx y hy
    cases μ
    · simp only [rungAdds, Bool.false_eq_true, ↓reduceIte]
      rw [count_pair_map hinj hx hy hxm.1 hxp.1 hym.1 hyp.1]
      exact ind_pair (adds_false hrs hXm hXp hX hYm hYp hY)
    · simp only [rungAdds, ↓reduceIte]
      rw [count_pair_map hinj hx hy hxm.1 hyp.1 hxp.1 hym.1]
      have h1 : g xm ≠ g yp := fun h =>
        hR.not_mem_both (x := xm) hR.xm_mem (by rw [hinj hxm.1 hyp.1 h]; exact hR.yp_mem)
      have h2 : g xp ≠ g ym := fun h =>
        hR.not_mem_both (x := xp) (by rw [hinj hxp.1 hym.1 h]; exact hR.ym_mem) hR.xp_mem
      have h3 : (ladMS M).count s(g xm, g yp) = 0 := by
        rw [← hmult xm hxm.1 yp hyp.1]; exact hR.noBond xm hR.xm_mem yp hR.yp_mem
      have h4 : (ladMS M).count s(g xp, g ym) = 0 := by
        rw [← hmult xp hxp.1 ym hym.1, Sym2.eq_swap]; exact hR.noBond ym hR.ym_mem xp hR.xp_mem
      exact ind_pair (adds_true hr2 hre hrM hrs hXm hXp hX hYm hYp hY h1 h2 h3 h4)
  rcases M with _ | N
  · -- the Q-block: the result is the double bond `p = q`
    right
    have hpq2 := lt_two_of_pair hpq
    have hpqne : g p ≠ g q := fun h => hB.2.2.1 (hinj hpV hqV h)
    have hab4 : 2 ≤ g a ∧ g a < 4 ∧ 2 ≤ g b ∧ g b < 4 ∧ g a ≠ g b := by unfold IsLadRung at huw; omega
    have hVX : X.verts = {p, a, b, q} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        have := hlt x hx
        have : g x = g p ∨ g x = g a ∨ g x = g b ∨ g x = g q := by omega
        rcases this with h | h | h | h
        · exact Or.inl (hinj hx hpV h)
        · exact Or.inr (Or.inl (hinj hx haV h))
        · exact Or.inr (Or.inr (Or.inl (hinj hx hbV h)))
        · exact Or.inr (Or.inr (Or.inr (hinj hx hqV h)))
      · rintro (rfl | rfl | rfl | rfl) <;> assumption
    have hpair : (X.verts.erase a).erase b = {p, q} := by
      rw [hVX]; ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3 | h3⟩
        · exact Or.inl h3
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact Or.inr h3
      · rintro (rfl | rfl)
        · exact ⟨Ne.symm hbp, Ne.symm hap, Or.inl rfl⟩
        · exact ⟨Ne.symm hbq, Ne.symm haq, Or.inr (Or.inr (Or.inr rfl))⟩
    refine ⟨hVX, isVineXU_I_of hB' (hV'.trans hpair) ?_,
      poles_of_pair (hR.union.trans hpair) hR.disj hR.xm_mem hR.xp_mem⟩
    rw [rungDel_mult, if_neg (not_mem_pair (Ne.symm hap) (Ne.symm hbp) (Ne.symm haq) (Ne.symm hbq)),
      hmult p hpV q hqV, hadd p hpV q hqV]
    have hr2' : r = 2 := by omega
    have hs : s(g p, g q) = s(0, 1) := by rw [Sym2.eq_iff]; omega
    have h01 : (ladMS 0).count s(0, 1) = 0 := by
      rw [count_ladMS, if_neg (by unfold IsLadRung; omega), if_neg (by unfold IsLadRail IsLadRail1; omega)]
    have hA1 : ladAdd₁ 0 r μ = s(0, 1) := by subst hr2'; cases μ <;> simp [ladAdd₁, ladLo, ladHi]
    have hA2 : ladAdd₂ 0 r μ = s(0, 1) := by subst hr2'; cases μ <;> simp [ladAdd₂, ladLo, ladHi]
    rw [hs, h01, hA1, hA2]
    simp
  · -- `N + 2` rungs: the result is the ladder with `N + 1` rungs
    left
    have hmemV : ∀ x ∈ (rungDel X a b xm xp ym yp μ).verts, x ∈ X.verts ∧ x ≠ a ∧ x ≠ b := by
      intro x hx; rw [hV', Finset.mem_erase, Finset.mem_erase] at hx; exact ⟨hx.2.2, hx.2.1, hx.1⟩
    have hoff : ∀ x ∈ X.verts, x ≠ a → x ≠ b → g x ≠ r ∧ g x ≠ r + 1 := by
      intro x hx hxa hxb
      have h1 : g x ≠ g a := fun h => hxa (hinj hx haV h)
      have h2 : g x ≠ g b := fun h => hxb (hinj hx hbV h)
      omega
    have hrN : r ≤ 2 * N + 4 := by omega
    refine isVineXU_II_iff.mpr ⟨hB', N, ladSig r μ ∘ g, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy h
      obtain ⟨hx1, hx2, hx3⟩ := hmemV x hx
      obtain ⟨hy1, hy2, hy3⟩ := hmemV y hy
      exact hinj hx1 hy1 (ladSig_inj μ hre (hoff x hx1 hx2 hx3).1 (hoff x hx1 hx2 hx3).2
        (hoff y hy1 hy2 hy3).1 (hoff y hy1 hy2 hy3).2 h)
    · ext Y
      simp only [Finset.mem_image, Finset.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨hx1, hx2, hx3⟩ := hmemV x hx
        exact ladSig_lt μ hre hrN (by have := hlt x hx1; omega) (hoff x hx1 hx2 hx3).1 (hoff x hx1 hx2 hx3).2
      · intro hY
        obtain ⟨U, hU, hU1, hU2, hσ⟩ := ladSig_surj μ hr2 hre hrN hY
        obtain ⟨x, hx, rfl⟩ := hpre U (by omega)
        refine ⟨x, ?_, hσ⟩
        rw [hV', Finset.mem_erase, Finset.mem_erase]
        refine ⟨fun h => ?_, fun h => ?_, hx⟩
        · rw [h] at hU1 hU2; omega
        · rw [h] at hU1 hU2; omega
    · have := lt_two_of_pair hpq
      simp only [Function.comp_apply, ladSig_of_lt μ (show g p < r by omega),
        ladSig_of_lt μ (show g q < r by omega)]
      exact hpq
    · intro x hx y hy
      obtain ⟨hx1, hx2, hx3⟩ := hmemV x hx
      obtain ⟨hy1, hy2, hy3⟩ := hmemV y hy
      rw [rungDel_mult, if_neg (not_mem_pair hx2 hx3 hy2 hy3), hmult x hx1 y hy1, hadd x hx1 y hy1,
        ← add_assoc, Function.comp_apply, Function.comp_apply]
      exact cnt_del μ hr2 hre hrN (hoff x hx1 hx2 hx3).1 (hoff x hx1 hx2 hx3).2 (hoff y hy1 hy2 hy3).1
        (hoff y hy1 hy2 hy3).2

end Graph

end WaveTurbulence.TVine.Core
